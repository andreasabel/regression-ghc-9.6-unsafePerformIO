This is a partial shrinkage of the Agda code base to reproduce a regression in the optimizer of GHC 9.6 concerning `unsafePerformIO` (used for debug messages).
- https://gitlab.haskell.org/ghc/ghc/-/issues/23699

With GHC 9.6.2, a debug message that is printed with `-O0` is not printed with `-O1`.

```shellsession
$ cabal run agda -w ghc-9.6.2 --builddir=dist0 -O0
ReduceM SHOULD ALSO PRINT THIS DEBUG MESSAGE!!!!!!!!!!!!! LET'S MAKE IT VERY LONG SO IT CANNOT BE OVERLOOKED!!!!!!!!!!!!!!!!!!!
agda: An internal error has occurred. Please report this as a bug.
Location of the error: __IMPOSSIBLE_VERBOSE__, called at src/full/Agda/ImpossibleTest.hs:22:11 in Agda-2.6.4-inplace-agda:Agda.ImpossibleTest
  impossibleTestReduceM, called at src/main/Main.hs:32:5 in Agda-2.6.4-inplace-agda:Main

$ cabal run agda -w ghc-9.6.2 -O1
agda: An internal error has occurred. Please report this as a bug.
Location of the error: __IMPOSSIBLE_VERBOSE__, called at src/full/Agda/ImpossibleTest.hs:22:11 in Agda-2.6.4-inplace-agda:Agda.ImpossibleTest
  impossibleTestReduceM, called at src/main/Main.hs:32:5 in Agda-2.6.4-inplace-agda:Main
```
Note that the separation of these builds in to two different `builddir`s is necessary because Cabal might confuse the builds otherwise:
- https://github.com/haskell/cabal/issues/7711

I shrank Agda from 426 modules to 142, it can likely be further shrunk (to 2 or 3 modules), but one has to proceed with care, as inlining code might make the issue go away.

Here are some branches where the issue has disappeared:
1. `lost-issue-inlining-impossibleTest`: inlining the module `Agda.ImpossibleTest`
2. `lost-issue-inlining-reportSLn`: inlining `reportSLn` into `__IMPOSSIBLE_VERBOSE__`

The latter modification was used to fix the motivating issue:
- https://github.com/agda/agda/issues/6728
- fixed in https://github.com/agda/agda/pull/6710/commits/4de3e5353cadd9a8e448af5f781701fa214ce9f3

This GHC issue for 8.8 and up might be related:
- https://gitlab.haskell.org/ghc/ghc/-/issues/19841
