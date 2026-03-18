[![CI](https://github.com/cmk/coapplicative/actions/workflows/ci.yml/badge.svg)](https://github.com/cmk/coapplicative/actions/workflows/ci.yml)

# coapplicative

Coapplicative and coapply functors — the duals of `Applicative`
and `Apply` — plus selective functors and partially distributive
functors (`Distributive1`).

## Overview

| Class | Dual of | Key operation |
|---|---|---|
| `Coapply f` | `Apply f` | `coapply :: f (a + b) -> f a + f b` |
| `Coapplicative f` | `Applicative f` | `copure :: f a -> a` |
| `Distributive1 g` | `Traversable1 t` | `distribute1 :: Coapply f => f (g a) -> g (f a)` |
| `Select f` | — | `Coapply f` + `Apply f` |
| `Selective f` | — | `Coapply f` + `Applicative f` |

## Coapply

### Theory

Where `Apply` combines two independent effects into one:

```haskell
class Functor f => Apply f where
  (<.>) :: f (a -> b) -> f a -> f b
```

`Coapply` does the opposite — it splits a sum-typed effect
into one of two independent effects:

```haskell
class Functor f => Coapply f where
  coapply :: f (a + b) -> f a + f b
```

The laws mirror `Apply`'s laws, dualized:

```
coapply . fmap Left  = Left
coeval  . fmap Left  = fmap Left
coeval  . fmap Right = fmap Right
```

where `coeval = coselect . coapply` "evaluates" a coapplicative
expression, exiting on the first `Left`.

### Example 1: splitting a list

```haskell
import Data.Functor.Coapply

-- Lists split on the first element:
>>> coapply [Left 1, Right 'a', Left 2]
Left [1, 2]
>>> coapply [Right 'a', Left 1, Right 'b']
Right "ab"
>>> coapply ([] :: [Either Int Char])
Left []
```

The first element determines the branch — `Left` collects all
lefts, `Right` collects all rights.

### Example 2: coeval for early exit

```haskell
import Data.Functor.Coapply
import Data.List.NonEmpty (NonEmpty(..))

-- coeval evaluates, exiting on the first Left:
>>> coeval $ Left "error" :| [Right "ok"]
Left "error" :| []
>>> coeval $ Right "ok" :| [Right "fine"]
Right "ok" :| [Right "fine"]

-- appendl accumulates Left errors:
>>> appendl "err1: " (Left "err2")
Left "err1: err2"
>>> appendl "err1: " (Right 42)
Right 42
```

## Coapplicative

### Theory

`Coapplicative` adds `copure` to `Coapply`, just as
`Applicative` adds `pure` to `Apply`:

```haskell
class Coapply f => Coapplicative f where
  copure :: f a -> a
```

`copure` extracts a single value from the functor. This is
the "default" or "head" value — the comonadic extract
restricted to functors (not requiring `Comonad`).

```
either (f . copure) (g . copure) . coapply = either f g . copure
```

### Example 1: extracting values

```haskell
import Control.Coapplicative

>>> copure (Identity 42)
42
>>> copure (Tagged @"label" "hello")
"hello"
>>> copure (1 :| [2, 3])
1
>>> copure ("key", "value")
"value"
>>> copure (const 42 :: Int -> Int)
42
```

### Example 2: composed coapplicatives

```haskell
import Control.Coapplicative
import Data.Functor.Compose

-- Coapplicative composes:
>>> copure (Compose (Identity (Identity 42)))
42
>>> copure (Compose ("key", Tagged @"t" True))
True

-- copure on (->) m uses mempty as the default input:
>>> copure ((\n -> n * 2) :: Sum Int -> Int)
0
```

## Select (Coapply + Apply)

### Theory

A **select** functor has both `Coapply` and `Apply` — it can
both split and combine effects. This enables branching:

```haskell
type Select f = (Coapply f, Apply f)

eitherS :: Select f => f (a + b) -> f (a -> c) -> f (b -> c) -> f c
branch  :: Select f => f Bool -> f a -> f a -> f a
```

`eitherS` dispatches on a sum: if the value is `Left a`,
apply the first function; if `Right b`, apply the second.
`branch` is the boolean specialization.

### Example 1: branching on booleans

```haskell
import Data.Functor.Coapply

>>> head $ branch (True :| []) (print "yes" :| []) (print "no" :| [])
"yes"
>>> head $ branch (False :| []) (print "yes" :| []) (print "no" :| [])
"no"
```

### Example 2: eitherS dispatch

```haskell
import Data.Functor.Coapply

-- Dispatch on Either, applying different functions:
>>> head $ eitherS (Left 42 :| []) (show :| []) (const "nope" :| [])
"42"
>>> head $ eitherS (Right () :| []) (show :| []) (const "nope" :| [])
"nope"
```

## Selective (Coapply + Applicative)

### Theory

**Selective** functors extend `Select` with `Applicative`,
enabling conditional effects that can skip unnecessary
computations:

```haskell
type Selective f = (Coapply f, Applicative f)

(<*?) :: Selective f => f (a + b) -> f (a -> b) -> f b
```

`<*?` is "select-apply": if the value is `Right b`, return it
directly (skipping the second effect). If `Left a`, apply the
function from the second effect. This is the key primitive for
selective functors as described by Mokhov et al.

### Example 1: conditional effects

```haskell
import Control.Coapplicative

-- whenS conditionally performs an effect:
>>> whenS [True] [putStrLn "hello"]
[()]
>>> whenS [False] [putStrLn "hello"]
[()]    -- effect skipped

-- fromMaybeS is a lifted fromMaybe:
>>> fromMaybeS [0] [Just 42]
[42]
>>> fromMaybeS [0] [Nothing]
[0]
```

### Example 2: short-circuiting validation

```haskell
import Control.Coapplicative

-- orElse returns the first Right, accumulating Left errors:
>>> orElse [Left "err1"] [Right "ok"]
[Right "ok"]
>>> orElse [Left "err1"] [Left "err2"]
[Left "err1err2"]

-- andAlso accumulates Rights, short-circuiting on Left:
>>> andAlso [Right "foo", Right "bar"] [Right "!"]
[Right "foo!", Right "bar!"]
>>> andAlso [Right "foo", Left 'e'] [Right "!"]
[Right "foo!"]

-- foldS generalizes folding with short-circuit:
>>> foldS [[Right "a"], [Right "b"], [Left "err"]]
[Right "ab"]
```

## Distributive1 (dual of Traversable1)

### Theory

Where `Traversable1` sequences effects through a structure:

```haskell
sequence1 :: (Traversable1 t, Apply f) => t (f a) -> f (t a)
```

`Distributive1` distributes a structure through effects:

```haskell
distribute1 :: (Distributive1 g, Coapply f) => f (g a) -> g (f a)
```

`Distributive1` is a partial version of `Distributive` — it
requires `Coapply` (non-empty split) rather than full
`Functor`, making it available for more types (like `[]`
and `NonEmpty`).

### Example 1: distributing lists

```haskell
import Data.Functor.Coapply

-- distribute1 transposes:
>>> distribute1 ["hi", "jk"]
["hj","ik"]

>>> distribute1 $ ('h' :| "i") :| ['j' :| "k"]
('h' :| "j") :| ['i' :| "k"]
```

### Example 2: cotraverse1

```haskell
import Data.Functor.Coapply

-- cotraverse1 is the dual of traverse1:
-- cotraverse1 f = fmap f . distribute1
>>> cotraverse1 head ["abc", "def"]
"ad"
>>> cotraverse1 last ["abc", "def"]
"cf"
```

## Modules

| Module | Contents |
|---|---|
| `Data.Functor.Coapply` | `Coapply` class, `apply`/`select`/`coselect`/`coeval`, `Select`, `eitherS`/`branch`/`bindBool`, `Distributive1` class, `cotraverse1` |
| `Control.Coapplicative` | `Coapplicative` class, `Selective`, `(<*?)`, `apS`, `eliminate`, `whenS`/`whileS`, `fromMaybeS`, `untilRight`, `(<\|\|>)`/`(<&&>)`, `anyS`/`allS`, `foldS`, `orElse`/`andAlso` |

## Instances

| Type | `Coapply` | `Coapplicative` | `Distributive1` |
|---|---|---|---|
| `Identity` | ✓ | ✓ | ✓ |
| `Tagged k` | ✓ | ✓ | ✓ |
| `(,) r` | ✓ | ✓ | — |
| `(->) r` (Monoid r) | ✓ | ✓ | ✓ |
| `Maybe` | ✓ | — | ✓ |
| `[]` | ✓ | — | ✓ |
| `NonEmpty` | ✓ | ✓ | ✓ |
| `Const r` | ✓ | — | — |
| `Compose f g` | ✓ (both) | ✓ (both) | ✓ (both) |
| `Product f g` | — | — | ✓ (both) |
| `ReaderT r m` | — | — | ✓ (m) |

## Dependencies

```
base, semigroupoids, tagged, transformers
```
