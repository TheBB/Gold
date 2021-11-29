cmake_minimum_required(VERSION 3.13)
project(gold)

set(CMAKE_CXX_STANDARD 17)
add_compile_options(-Wall -Wextra -Wno-unused-parameter -pedantic)

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/lib)

target_include_directories(gold PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)
target_include_directories(gold INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/include)

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/bin)
target_link_libraries(gold-to-json gold)
