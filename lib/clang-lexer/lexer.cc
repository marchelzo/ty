#include <cstdlib>
#include <cstring>
#include <vector>
#include <clang/Basic/Diagnostic.h>
#include <clang/Basic/DiagnosticOptions.h>
#include <clang/Basic/FileManager.h>
#include <clang/Basic/IdentifierTable.h>
#include <clang/Basic/SourceManager.h>
#include <clang/Lex/Lexer.h>
#include <llvm/Support/MemoryBuffer.h>

struct rawtoken {
        unsigned start, end, kind, line, sol;
        char *spelling;
};

extern "C" void
ty_clang_lex_free(rawtoken *tokens, unsigned count)
{
        for (unsigned i = 0; i < count; ++i) {
                free(tokens[i].spelling);
        }
        free(tokens);
}

extern "C" rawtoken *
ty_clang_lex(char const *source, size_t size, int trigraphs, unsigned *count)
{
        clang::LangOptions opts;
        opts.C99 = opts.C11 = opts.C17 = opts.C23 = true;
        opts.LineComment = opts.Digraphs = opts.HexFloats = opts.Bool = true;
        opts.Trigraphs = trigraphs;
        clang::DiagnosticsEngine diagnostics(new clang::DiagnosticIDs, new clang::DiagnosticOptions);
        diagnostics.setSuppressAllDiagnostics(true);
        clang::FileManager files(clang::FileSystemOptions{});
        clang::SourceManager sources(diagnostics, files);
        auto buffer = llvm::MemoryBuffer::getMemBufferCopy(llvm::StringRef(source, size));
        auto file = sources.createFileID(std::move(buffer));
        clang::Lexer lexer(file, sources.getBufferOrFake(file), sources, opts);
        clang::IdentifierTable identifiers(opts);
        lexer.SetCommentRetentionState(true);
        std::vector<rawtoken> tokens;
        clang::Token token;
        for (;;) {
                lexer.LexFromRawLexer(token);
                if (token.is(clang::tok::eof)) {
                        break;
                }
                auto spelling = clang::Lexer::getSpelling(token, sources, opts);
                unsigned kind = 0;
                if (token.is(clang::tok::raw_identifier)) {
                        kind = identifiers.get(spelling).getTokenID() == clang::tok::identifier ? 2 : 1;
                } else if (token.isLiteral()) {
                        kind = 3;
                } else if (token.is(clang::tok::comment)) {
                        kind = 4;
                }
                unsigned start = sources.getFileOffset(token.getLocation());
                char *text = strdup(spelling.c_str());
                if (text == nullptr) {
                        std::abort();
                }
                tokens.push_back({start, start + token.getLength(), kind,
                        sources.getSpellingLineNumber(token.getLocation()), token.isAtStartOfLine(), text});
        }
        *count = tokens.size();
        auto out = static_cast<rawtoken *>(calloc(tokens.size() + 1, sizeof (rawtoken)));
        if (out == nullptr) {
                std::abort();
        }
        if (!tokens.empty()) {
                memcpy(out, tokens.data(), tokens.size() * sizeof (rawtoken));
        }
        return out;
}
