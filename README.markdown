# recursion-schemes

[![Hackage](https://img.shields.io/hackage/v/recursion-schemes.svg)](https://hackage.haskell.org/package/recursion-schemes) [![Build Status](https://github.com/ekmett/recursion-schemes/workflows/Haskell-CI/badge.svg)](https://github.com/ekmett/recursion-schemes/actions?query=workflow%3AHaskell-CI)

## What is a recursion scheme?

Many recursive functions share the same structure, e.g. pattern-match on the input and, depending on the data constructor, either recur on a smaller input or terminate the recursion with the base case. Another one: start with a seed value, use it to produce the first element of an infinite list, and recur on a modified seed in order to produce the rest of the list. Such a structure is called a recursion scheme.

## Benefits

### Clearer

Each recursion scheme has a unique name, such as "fold" and "unfold"; or, if you prefer the fancy names, "catamorphism" and "anamorphism". If you program with others, it can be useful to have names to refer to those recursion patterns, so you can discuss which type of recursion is the most appropriate for the problem at hand. Even if you program alone, having names with which to clearly label those different solutions can help to structure your thoughts while writing recursive functions.

This library lists the most common recursion schemes, and also provides an implementation corresponding to each one. The idea is that a recursive function may be broken into two parts: the part which is the same in all the recursive functions which follow a given recursion scheme, and the part which is different in each function. Our implementation performs the recursive, common part, and takes as input a function which performs the non-recursive, unique part.

If you use those implementations instead of making explicit recursive calls, your code will simultaneously become clearer (to those who are familiar with recursion schemes) and more obscure (to those who aren't). Obviously, if one knows how to read and understand recursive code but does not know what e.g. `para` means, then the version which uses `para` will look needlessly obfuscated compared to the version they already know how to read. But if one is familiar with `para`, then seeing this familiar name will instantly clarify that this is a path-copying function in the style of `Map.insert`, which allocates new nodes along a path from a node to the root but leaves the rest of the nodes untouched. This is a very useful starting point, guiding the reader to look for the logic which decides which sub-trees to drill through and which sub-trees to leave untouched. In contrast, with the general-recursion version, the reader has no such starting point and must thus read through the entire function (or guess based on the function's name) before they can infer that kind of big picture information.

### Faster

Using recursion schemes can guide you towards optimizations. When multiple functions are composed, Haskellers often use equational reasoning in order to rearrange those compositions into equivalent compositions which compute the same result, but do so in a different, possibly more efficient manner. When the recursive and non-recursive portions of a function are written separately, more equations become available, as they have more pieces to work with. The paper [Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire](https://maartenfokkinga.github.io/utwente/mmf91m.pdf) has a lot more details on that subject.

### Safer

Using recursion schemes can help you to avoid accidentally writing infinite or non-productive loops. For example, when producing an infinite list, it would be a mistake to look at the result of the recursive call in order to decide which element to produce as the head of the list, because that recursive call will itself look at its recursive call, etc., and so the information will never be returned. With `ana`, the non-recursive function you need to provide as input intentionally does not have access to the result of the recursive call, so you cannot make that mistake.

### Composable

Many recursion schemes can be implemented in terms of each other. So if you notice that the non-recursive functions you provide themselves seem to share a common pattern, you might be accidentally reimplementing an existing recursion scheme which already has those common parts builtin; or maybe you have stumbled upon a new recursion scheme which does not yet have a name, and which you may want to implement yourself.

One way to implement such a custom recursion scheme is to combine the features of existing recursion schemes. For example, a "paramorphism" gives the non-recursive function access to the original sub-trees, a "zygomorphism" gives that function access to auxiliary results computed from those sub-trees, and so the combined "zygomorphic paramorphism" gives that function access to both the original sub-trees and the auxiliary results. In order to construct such combinations, most of our recursion schemes come in a generalized variant, e.g. `gzygo`, and in a "distributive law transformer" variant, e.g. `distZygoT`. Just like monad transformers, distributive law transformers can be combined into stacks, and like monad transformers, the order in which you combine the layers determines how the layers interact with each other. Apply a generalized recursion scheme to a stack of distributive laws in order to obtain a recursion scheme which has both the features of the generalized recursion scheme and those of the distributive laws.

## Contributing

Contributions and bug reports are welcome!

Please feel free to contact us by opening a github issue or by hopping onto the #haskell IRC channel on irc.freenode.net.
