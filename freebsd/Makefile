PORTNAME=	ty
DISTVERSIONPREFIX=	v
DISTVERSION=	0.1
CATEGORIES=	lang

MAINTAINER=	bradgaragan@gmail.com
COMMENT=	Ty programming language
WWW=		https://github.com/marchelzo/ty

LICENSE=	MIT
LICENSE_FILE=	${WRKSRC}/LICENSE

RUN_DEPENDS=	terminfo-db>0:misc/terminfo-db

BUILD_DEPENDS=	gperf:devel/gperf \
		luajit:lang/luajit \
		ninja:devel/ninja \
		${LOCALBASE}/lib/libffi.a:devel/libffi \
		${LOCALBASE}/lib/libmimalloc.a:devel/mimalloc \
		${LOCALBASE}/lib/libpcre2-8.a:devel/pcre2 \
		${LOCALBASE}/lib/libxxhash.a:devel/xxhash

LIB_DEPENDS=	libutf8proc.so:textproc/utf8proc

USES=		cmake pkgconfig sqlite

USE_GITHUB=	yes
GH_ACCOUNT=	marchelzo

CMAKE_ARGS=	-DUSE_SYSTEM_DEPS:BOOL=ON \
		-DUSE_NSYNC:BOOL=ON \
		-DCMAKE_BUILD_TYPE:STRING=Release

PLIST_SUB=	TYMODDIR="${TYMODDIR}"

TYMODDIR=	lib/ty

.include <bsd.port.mk>
