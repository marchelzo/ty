PORTNAME=	ty
DISTVERSION=	0.1
CATEGORIES=	lang

MAINTAINER=	bradgaragan@gmail.com
COMMENT=	The Ty programming language
WWW=		https://github.com/marchelzo/ty

LICENSE=	MIT
LICENSE_FILE=	${WRKSRC}/LICENSE

BUILD_DEPENDS=	gperf:devel/gperf \
		luajit:lang/luajit \
		ninja:devel/ninja

RUN_DEPENDS=	terminfo-db>0:devel/terminfo-db

LIB_DEPENDS=	libffi.so:devel/libffi \
		libmimalloc.so:devel/mimalloc \
		libpcre2-8.so:devel/pcre2 \
		libutf8proc.so:textproc/utf8proc \
		libxxhash.so:devel/xxhash

USES=		cmake pkgconfig sqlite

USE_GITHUB=	yes
GH_ACCOUNT=	marchelzo

CMAKE_ARGS=	-DUSE_SYSTEM_DEPS:BOOL=ON \
		-DUSE_NSYNC:BOOL=ON \
		-DCMAKE_BUILD_TYPE:STRING=Release

PLIST_SUB=	TYMODDIR="${TYMODDIR}"

TYMODDIR=	lib/ty

.include <bsd.port.mk>
