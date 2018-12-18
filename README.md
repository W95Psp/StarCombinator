# StarCombinator
Tiny parser combinator library for FStar

## How to use
Just open the main module:
```fstar
open StarCombinator
```

- You can chain two parsers `a` (outputing things of type `t`) `b` (outputing things of type `y`): `a <*> b` will make a parser of type `(a * b)`
- `a <*>> b` will chain `a` and `b` omiting the result of `a` (`a <<*> b` exists as well)
- You can parse either `a` or `b` (`a` and `b` being parsers of a same type `t`) with `a <|> b`, that will make a parser of type `t`
- `a </> b` parse either `a` or `b`, but of different types `t` `u`, making some `parser (either t u)`
- `a <?> "some error message"` attribute a custom error message for any parser
- `maybe` `many` `many1`
- `keyword "hey"` match `"hey"` and ensure there is no letter after or before it
- `notFollowedBy` `lookAhead`
- `delayMe p` with `p: () -> parser t` (for some type `t`) makes a parser behave as a lazy function: then you can write stuff like `let myParser () = (number <*>> keyword "+") <<*> maybe (delayMe myParser)`
- suppose `p: parser t`, then `f @<< p` (with `f: t -> u`) is of type `parser u`: it maps the output of `p` using `f`. For instance here is a parser for any number of additions (i.e. `10 + 30 + 2`, `6 + 36` or `42`): 

```fstar
let myParser (): parser int
	= (fun (leftNumber, right) -> match right with
		| None             -> leftNumber
		| Some rightNumber -> leftNumber + rightNumber
	) *<< (
		     (number <*>> keyword "+")
		<<*> maybe (delayMe myParser)
	)
```

## Examples
The files `StarCombinator.Examples.fst` and `StarCombinator.Examples.While.fst` contains examples.
