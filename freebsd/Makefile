PORTNAME=	ty
DISTVERSION=	0.1
CATEGORIES=	lang

MAINTAINER=	bradgaragan@gmail.com
COMMENT=	The Ty programming language
WWW=		https://github.com/marchelzo/ty

LICENSE=	MIT
LICENSE_FILE=	${WRKSRC}/LICENSE

BUILD_DEPENDS=	gperf:devel/gperf \
		ninja:devel/ninja

LIB_DEPENDS=	libffi.so:devel/libffi \
		libmimalloc.so:devel/mimalloc \
		libpcre2-8.so:devel/pcre2 \
		libutf8proc.so:textproc/utf8proc \
		libxxhash.so:devel/xxhash

USES=		cmake pkgconfig sqlite

USE_GITHUB=	yes
GH_ACCOUNT=	marchelzo

CMAKE_ARGS=	-DUSE_SYSTEM_DEPS:BOOL=ON \
		-DCMAKE_BUILD_TYPE:STRING=Release

PLIST_SUB=	TYMODDIR="${TYMODDIR}"

TYMODDIR=	lib/ty

OPTIONS_DEFINE=		JIT NSYNC
OPTIONS_DEFAULT=	NSYNC

JIT_DESC=		Enable JIT code generation (requires luajit)
JIT_CMAKE_BOOL_OFF=	NO_JIT
JIT_BUILD_DEPENDS=	luajit:lang/luajit

NSYNC_DESC=		Use nsync synchronization primitives
NSYNC_CMAKE_BOOL=	USE_NSYNC

.include <bsd.port.mk>
