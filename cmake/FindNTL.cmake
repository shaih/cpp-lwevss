# Copyright (C) 2021, LWE-PVSS
#
# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject
# to the following conditions:
#
# The above copyright notice and this permission notice shall be included
# in all copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
# OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
# THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
# OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
# ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
# OTHER DEALINGS IN THE SOFTWARE.
#
# January 2021, adapted from https://github.com/homenc/HElib/blob/master/cmake/FindNTL.cmake

# Use cmake standard find_library package
include(FindPackageHandleStandardArgs)

# Standard `lib` and system specific `lib32/64` directory.
list(APPEND lib_suffixes "lib" "${CMAKE_INSTALL_LIBDIR}")

# Standard `include` system specific directory (usually the same).
list(APPEND header_suffixes "include/NTL" "${CMAKE_INSTALL_INCLUDEDIR}/NTL")

# If CMAKE_LIBRARY_ARCHITECTURE is defined (e.g.: `x86_64-linux-gnu`) add that
# after `lib` and `lib32/64` and after `include` suffixes(required for Ubuntu)
if (CMAKE_LIBRARY_ARCHITECTURE)
  list(APPEND lib_suffixes
       "lib/${CMAKE_LIBRARY_ARCHITECTURE}"
       "${CMAKE_INSTALL_LIBDIR}/${CMAKE_LIBRARY_ARCHITECTURE}")
  list(APPEND header_suffixes
       "include/${CMAKE_LIBRARY_ARCHITECTURE}/NTL"
       "${CMAKE_INSTALL_INCLUDEDIR}/${CMAKE_LIBRARY_ARCHITECTURE}/NTL")
endif (CMAKE_LIBRARY_ARCHITECTURE)

find_library(NTL_LIBRARIES
               NAMES ntl libntl
               PATH_SUFFIXES "${lib_suffixes}"
               DOC "NTL library")

find_path(NTL_HEADERS
            NAMES config.h
            PATH_SUFFIXES ${header_suffixes}
            DOC "NTL headers")


unset(lib_suffixes)
unset(header_suffixes)

# Check the library has been found, handle QUIET/REQUIRED arguments and set
# NTL_FOUND accordingly or raise the error
find_package_handle_standard_args(NTL
                                  REQUIRED_VARS NTL_LIBRARIES NTL_HEADERS)

set(NTL_INCLUDE_PATHS "${NTL_HEADERS}/..")

# Mark NTL_LIBRARIES NTL_INCLUDE_PATHS as advanced variables
mark_as_advanced(NTL_LIBRARIES NTL_INCLUDE_PATHS)
