# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/invariant_synthesis_main.cpp
)
add_library(invariant-synthesis-lib ${sources})

generic_includes(invariant-synthesis-lib)

target_link_libraries(invariant-synthesis-lib
    ansi-c
    cpp
    goto-checker
    goto-instrument-lib
    goto-programs
    langapi
    pointer-analysis
    solvers
    util
)

# Executable
add_executable(invariant-synthesis invariant_synthesis_main.cpp)
target_link_libraries(invariant-synthesis invariant-synthesis-lib)
install(TARGETS invariant-synthesis DESTINATION ${CMAKE_INSTALL_BINDIR})
