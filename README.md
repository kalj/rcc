# rcc - A C compiler in rust

## Current limitations

* Only `int`, `void`, and pointers to either of those are supported.
* No arrays. 
* No structs.
* No preprocessor directives.
* No C strings / `char` arrays.
* No type qualifiers (`register`, `volatile`, `inline`, etc).
* No variadic functions.
* Probably many more restrictions...

## Credits
Inspired by a series of blog posts by Nora Sandler: https://norasandler.com/2017/11/29/Write-a-Compiler.html

