cmake_minimum_required(VERSION 3.0.0)
project(lwe-pvss VERSION 0.1.0)

# Use -std=c++17 as default.
set(CMAKE_CXX_STANDARD 17)

# Dependencies are GMP/NTL and libsodium

# Add directories for extra cmake files, e.g. to find NTK and other libraries
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

find_package(GMP)
# define the following variables (see ./cmake/FindNTL.make)
#   GMP_FOUND
#   GMP_LIBRARIES
#   GMP_HEADERS

find_package(NTL)
# define the following variables (see ./cmake/FindNTL.make)
#   NTL_FOUND
#   NTL_LIBRARIES
#   NTL_HEADERS

find_package(sodium)
# define the following variables (see ./cmake/FindSodium.make)
#   sodium_FOUND
#   sodium_INCLUDE_DIR
#   sodium_LIBRARY_DEBUG
#   sodium_LIBRARY_RELEASE

include_directories("${CMAKE_CURRENT_SOURCE_DIR}/include")

# Source files are found under the src directory
file(GLOB SOURCES src/*/*.cpp src/libmerlin/merlin.c)
add_library(lwe-pvss STATIC ${SOURCES})

set(PROJECT_LIBS lwe-pvss ${sodium_LIBRARY_DEBUG} ${NTL_LIBRARIES} ${GMP_LIBRARIES} pthread)
# SET(EXTRAOBJS "${CMAKE_CURRENT_SOURCE_DIR}/src/libmerlin/merlin.o")

add_executable(lwe-pvss-main src/main.cpp)
target_link_libraries(lwe-pvss-main PUBLIC ${PROJECT_LIBS})

include(CTest)
enable_testing()
add_subdirectory("${CMAKE_CURRENT_SOURCE_DIR}/tests")

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
