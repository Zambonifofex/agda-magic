GHC API Haskell FFI directive generation for Agda
===

What is this?
---

This is a Haskell project that aims to allow people to use Haskell libraries from Agda directly, without having to write the FFI directive for themselves.

It uses [the GHC API][GHC API] to inspect Haskell intermediate files (`.hi`) to generate Agda files containing datatype and record type declarations corresponding to their Haskell counterparts, as well as postulates for the Haskell functions. Although it has yet to be implemented, the goal is to also generate FFI directives to associate the generated Agda postulates with their Haskell counterparts.

[GHC API]: https://hackage.haskell.org/package/ghc

Building
---

The only way I have tried building and using the project is by running `cabal new-build`, and running the generated executable through its full path.

Patches
---

Patches, issue reports, suggestions, as well as general discussions about the project are really appreciated!

License
---

I don’t know. &#x1F937; If you have any suggestions for a good license, feel free to let me know! I’m inclined to use [Creative Commons Zero][CC0] in the future.

[CC0]: https://creativecommons.org/publicdomain/zero/1.0/
