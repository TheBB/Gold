cmake_minimum_required(VERSION 3.13)

set(
    CMAKE_TOOLCHAIN_FILE
    ${CMAKE_CURRENT_SOURCE_DIR}/submodules/vcpkg/scripts/buildsystems/vcpkg.cmake
    CACHE STRING "Vcpkg toolchain file"
)

project(gold)

option(GOLD_BUILD_UTILS "Build utilities" ON)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_VISIBILITY_PRESET hidden)

set(GOLD_ROOT_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(GOLD_BINARY_ROOT_DIR ${CMAKE_CURRENT_BINARY_DIR})

if(CMAKE_COMPILER_IS_GNUCXX)
    add_compile_options(-Wall -Wextra -Wno-unused-parameter -pedantic)
endif()

if(MSVC)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /bigobj")
endif()

if(APPLE)
    find_package(Boost COMPONENTS filesystem)
endif()

if(GOLD_BUILD_UTILS)
    find_package(cxxopts CONFIG REQUIRED)
endif()

find_package(fmt CONFIG REQUIRED)
find_package(pegtl CONFIG REQUIRED)

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
