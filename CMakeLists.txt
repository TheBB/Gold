cmake_minimum_required(VERSION 3.13)
project(gold)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)
set(CMAKE_CXX_STANDARD 17)
add_compile_options(-Wall -Wextra -Wno-unused-parameter -pedantic)

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/submodules/pegtl EXCLUDE_FROM_ALL)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/submodules/pybind11 EXCLUDE_FROM_ALL)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/lib)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/bin)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/python)
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

target_include_directories(gold-nostdlib PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)
target_include_directories(gold-nostdlib INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/include)
target_include_directories(gold-stdlib PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/stdlib)
target_include_directories(gold-to-json PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/vendor)
target_include_directories(pygold PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)

target_link_libraries(gold-serialize gold-nostdlib)
target_link_libraries(gold-to-json gold-nostdlib gold-stdlib)
target_link_libraries(gold-stdlib gold-nostdlib)
target_link_libraries(pygold PRIVATE gold-nostdlib gold-stdlib)

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/tests EXCLUDE_FROM_ALL)
target_link_libraries(gold-test PRIVATE gold-nostdlib gold-stdlib)
target_include_directories(gold-test PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/lib/include)

enable_testing()
add_test(NAME parsing COMMAND $<TARGET_FILE:gold-test> [parsing])
add_test(NAME serialization COMMAND $<TARGET_FILE:gold-test> [serialization])
add_test(NAME bindings COMMAND $<TARGET_FILE:gold-test> [bindings])
add_test(NAME evaluate COMMAND $<TARGET_FILE:gold-test> [evaluate])
add_custom_target(check COMMAND cmake --build ${CMAKE_CURRENT_BINARY_DIR} --target test DEPENDS gold-test)

# install(TARGETS gold gold-to-json)
# install(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/share/ TYPE DATA)
