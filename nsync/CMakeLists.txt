cmake_minimum_required (VERSION 2.8.12...4.0)

if ("${CMAKE_MAJOR_VERSION}X" STREQUAL "2X")
	project (nsync)
else ()
	file (STRINGS VERSION VERSION_STRING)
	cmake_policy(SET CMP0048 NEW)
	project (nsync VERSION "${VERSION_STRING}")
endif ()

set (CMAKE_POSITION_INDEPENDENT_CODE ON)

# -----------------------------------------------------------------
# Functions to set common options on targets.
function (set_c_target tgtname files)
	if ("${CMAKE_SYSTEM_NAME}X" STREQUAL "LinuxX")
		target_include_directories ("${tgtname}" BEFORE PRIVATE
			"${PROJECT_SOURCE_DIR}/platform/linux"
		)
	endif ()
endfunction (set_c_target)

# -----------------------------------------------------------------
# Platform dependencies

set (NSYNC_POSIX_SRC
	"platform/posix/src/nsync_panic.c"
	"platform/posix/src/per_thread_waiter.c"
	"platform/posix/src/time_rep.c"
	"platform/posix/src/yield.c"
)

if ("${CMAKE_C_COMPILER_ID}X" STREQUAL "MSVCX")
	add_compile_options (/wd4057 /wd4100 /wd4152 /wd4242 /wd4244 /wd4255 /wd4267)
	add_compile_options (/wd4365 /wd4389 /wd4458 /wd4571 /wd4625 /wd4626 /wd4668)
	add_compile_options (/wd4702 /wd4710 /wd4774 /wd4820 /wd5026 /wd5027 /wd5039)
	add_compile_options (/wd5045)
endif ()

# Pick the include directory for the operating system.
if ("${CMAKE_SYSTEM_NAME}X" STREQUAL "WindowsX")
	include_directories ("${PROJECT_SOURCE_DIR}/platform/win32")

	set (NSYNC_OS_SRC
		${NSYNC_POSIX_SRC}
		"platform/win32/src/clock_gettime.c"
		"platform/win32/src/init_callback_win32.c"
		"platform/win32/src/nanosleep.c"
		"platform/win32/src/nsync_semaphore_win32.c"
		"platform/win32/src/pthread_cond_timedwait_win32.c"
		"platform/win32/src/pthread_key_win32.cc"
	)
elseif ("${CMAKE_SYSTEM_NAME}X" STREQUAL "DarwinX")
	include_directories ("${PROJECT_SOURCE_DIR}/platform/macos")
	set (NSYNC_POSIX ON)

	set (NSYNC_OS_EXTRA_SRC
		"platform/posix/src/clock_gettime.c"
		"platform/posix/src/nsync_semaphore_mutex.c"
	)
elseif ("${CMAKE_SYSTEM_NAME}X" STREQUAL "LinuxX")
	set (NSYNC_POSIX ON)

	set (NSYNC_OS_EXTRA_SRC
		"platform/linux/src/nsync_semaphore_futex.c"
	)
elseif ("${CMAKE_SYSTEM_NAME}X" STREQUAL "NetBSDX")
	include_directories ("${PROJECT_SOURCE_DIR}/platform/netbsd")
	set (NSYNC_POSIX ON)

	set (NSYNC_OS_EXTRA_SRC
		"platform/posix/src/nsync_semaphore_mutex.c"
	)
elseif ("${CMAKE_SYSTEM_NAME}X" STREQUAL "FreeBSDX")
	include_directories ("${PROJECT_SOURCE_DIR}/platform/freebsd")
	set (NSYNC_POSIX ON)

	set (NSYNC_OS_EXTRA_SRC
		"platform/posix/src/nsync_semaphore_mutex.c"
	)
elseif ("${CMAKE_SYSTEM_NAME}X" STREQUAL "OpenBSDX")
	include_directories ("${PROJECT_SOURCE_DIR}/platform/openbsd")
	set (NSYNC_POSIX ON)

	set (NSYNC_OS_EXTRA_SRC
		"platform/posix/src/nsync_semaphore_mutex.c"
	)
else ()
	set (NSYNC_POSIX ON)

	set (NSYNC_OS_EXTRA_SRC
		"platform/posix/src/nsync_semaphore_mutex.c"
	)
endif ()

# Pick the include directory for the compiler.
if ("${CMAKE_C_COMPILER_ID}X" STREQUAL "GNUX")
	include_directories ("${PROJECT_SOURCE_DIR}/platform/gcc")
	set (THREADS_HAVE_PTHREAD_ARG ON)
elseif ("${CMAKE_C_COMPILER_ID}X" STREQUAL "ClangX")
	include_directories ("${PROJECT_SOURCE_DIR}/platform/clang")
	set (THREADS_HAVE_PTHREAD_ARG ON)
elseif ("${CMAKE_C_COMPILER_ID}X" STREQUAL "MSVCX")
	include_directories ("${PROJECT_SOURCE_DIR}/platform/msvc")
endif ()

if (NSYNC_POSIX)
	include_directories ("${PROJECT_SOURCE_DIR}/platform/posix")

	set (NSYNC_OS_SRC
		${NSYNC_POSIX_SRC}
		${NSYNC_OS_EXTRA_SRC}
	)
endif ()

# Pick the include directory for the architecture.
if (("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "x86_64X") OR
    ("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "amd64X") OR
    ("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "AMD64X"))
	include_directories ("${PROJECT_SOURCE_DIR}/platform/x86_64")
elseif (("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "x86_32X") OR
	("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "i386X") OR
	("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "i686X"))
	include_directories ("${PROJECT_SOURCE_DIR}/platform/x86_32")
elseif (("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "armv6lX") OR
	("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "armv7lX") OR
	("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "armX"))
	include_directories ("${PROJECT_SOURCE_DIR}/platform/arm")
elseif (("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "aarch64X") OR
	("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "arm64X"))
	include_directories ("${PROJECT_SOURCE_DIR}/platform/aarch64")
elseif (("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "ppcX") OR
	("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "ppc32X"))
	include_directories ("${PROJECT_SOURCE_DIR}/platform/ppc32")
elseif (("${CMAKE_SYSTEM_PROCESSOR}X" STREQUAL "ppc64X"))
	include_directories ("${PROJECT_SOURCE_DIR}/platform/ppc64")
endif ()

# Windows uses some include files from the posix directory also.
if ("${CMAKE_SYSTEM_NAME}X" STREQUAL "WindowsX")
	include_directories ("${PROJECT_SOURCE_DIR}/platform/posix")
endif ()

# -----------------------------------------------------------------

include_directories ("${PROJECT_SOURCE_DIR}/public")
include_directories ("${PROJECT_SOURCE_DIR}/internal")

set (NSYNC_COMMON_SRC
	"internal/common.c"
	"internal/counter.c"
	"internal/cv.c"
	"internal/debug.c"
	"internal/dll.c"
	"internal/mu.c"
	"internal/mu_wait.c"
	"internal/note.c"
	"internal/once.c"
	"internal/sem_wait.c"
	"internal/time_internal.c"
	"internal/wait.c"
)

add_library (nsync ${NSYNC_COMMON_SRC} ${NSYNC_OS_SRC})
set_target_properties (nsync PROPERTIES
	VERSION ${PROJECT_VERSION}
	SOVERSION ${PROJECT_VERSION_MAJOR})
target_include_directories (nsync PUBLIC
	$<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/public>
	$<INSTALL_INTERFACE:include>)

set_c_target (nsync "${NSYNC_COMMON_SRC} ${NSYNC_OS_SRC}")

find_package (Threads REQUIRED)
set (THREADS_PREFER_PTHREAD_FLAG ON)
if (THREADS_HAVE_PTHREAD_ARG)
	target_compile_options (nsync PUBLIC "-pthread")
endif ()
if (CMAKE_THREAD_LIBS_INIT)
	target_link_libraries (nsync "${CMAKE_THREAD_LIBS_INIT}")
endif ()
