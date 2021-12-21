cmake_minimum_required(VERSION 3.13)

project(gold)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_VISIBILITY_PRESET hidden)

if(CMAKE_COMPILER_IS_GNUCXX)
    add_compile_options(-Wall -Wextra -Wno-unused-parameter -pedantic)
endif()

add_subdirectory(submodules/cxxopts EXCLUDE_FROM_ALL)
add_subdirectory(submodules/fmt EXCLUDE_FROM_ALL)
add_subdirectory(submodules/json EXCLUDE_FROM_ALL)
add_subdirectory(submodules/pegtl EXCLUDE_FROM_ALL)

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/lib)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/bin)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/stdlib)

add_custom_target(stdlib-serialize ALL)

foreach(LIBFILE ${GOLD_STDLIBS})
    set(FIN ${CMAKE_CURRENT_BINARY_DIR}/stdlib/${LIBFILE}.serialized.c)
    set(OUT ${CMAKE_CURRENT_BINARY_DIR}/stdlib/${LIBFILE}.serialized)
    set(IN ${CMAKE_CURRENT_SOURCE_DIR}/stdlib/${LIBFILE})
    add_custom_command(
        COMMAND xxd -i ${LIBFILE}.serialized ${FIN}
        OUTPUT ${FIN} DEPENDS ${OUT}
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/stdlib
    )
    add_custom_command(
        COMMAND $<TARGET_FILE:gold-serialize> ${IN} ${OUT}
        OUTPUT ${OUT} DEPENDS ${IN}
    )
    add_custom_target(stdlib-serialize-${LIBFILE} DEPENDS ${FIN})
    add_dependencies(stdlib-serialize stdlib-serialize-${LIBFILE})
endforeach()

add_dependencies(gold-stdlib stdlib-serialize)

enable_testing()
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/tests EXCLUDE_FROM_ALL)
add_custom_target(check COMMAND cmake --build ${CMAKE_BINARY_DIR} --target test DEPENDS gold-test)
