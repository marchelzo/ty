if (WIN32)
        add_library(nsync INTERFACE)
        return()
endif ()

file(GLOB NSYNC_SRC CONFIGURE_DEPENDS
        *.c
        compat/*.c
        mem/*.c
)

add_library(nsync STATIC ${NSYNC_SRC})

set_target_properties(nsync PROPERTIES POSITION_INDEPENDENT_CODE ON C_STANDARD 11)

target_compile_definitions(nsync PRIVATE _GNU_SOURCE)

target_include_directories(nsync PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/include)

find_package(Threads REQUIRED)
target_link_libraries(nsync PUBLIC Threads::Threads)
