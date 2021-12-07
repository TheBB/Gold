cmake_minimum_required(VERSION 3.13)
project(gold)

set(CMAKE_CXX_STANDARD 17)
add_compile_options(-Wall -Wextra -Wno-unused-parameter -pedantic)

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/submodules/pegtl)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/lib)

target_include_directories(gold PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)
target_include_directories(gold INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/include)

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/bin)
target_link_libraries(gold-to-json gold)
target_include_directories(gold-to-json PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/lib/include)

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/tests)
target_link_libraries(gold-test PRIVATE gold)
target_include_directories(gold-test PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/lib/include)

enable_testing()
add_test(NAME parsing COMMAND $<TARGET_FILE:gold-test> [parsing])
add_test(NAME bindings COMMAND $<TARGET_FILE:gold-test> [bindings])
