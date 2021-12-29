set(GOLD_PRIVATE_INCLUDES ${CMAKE_CURRENT_SOURCE_DIR}/include PARENT_SCOPE)


add_library(
    gold-nostdlib
    ${CMAKE_CURRENT_SOURCE_DIR}/gold.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/parsing.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/ast.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/serialization.cpp
)

target_include_directories(gold-nostdlib PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)
target_include_directories(gold-nostdlib PUBLIC ${GOLD_ROOT_DIR}/include)
target_link_libraries(gold-nostdlib fmt::fmt taocpp::pegtl)



add_library(
    gold-stdlib OBJECT
    ${CMAKE_CURRENT_SOURCE_DIR}/stdlib.cpp
)

target_include_directories(gold-stdlib PRIVATE ${GOLD_BINARY_ROOT_DIR}/stdlib)
target_link_libraries(gold-stdlib gold-nostdlib)
