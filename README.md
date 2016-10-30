tensor-ops
==========

[![Build Status](https://travis-ci.org/mstksg/tensor-ops.svg?branch=master)](https://travis-ci.org/mstksg/tensor-ops)

*tensor-ops* is a library for specifying type-safe tensor manipulations that
can be automatically differentiated using reverse-mode AD for automatic
gradient descent.

The center of everything is a data type [`TOp`][top] that represents a tensor operation:

[top]: https://mstksg.github.io/tensor-ops/TensorOps-Types.html#t:TOp

~~~haskell
TOp :: [[k]] -> [[k]] -> Type
~~~

The first argument is a list of the dimensions of the input tensors, and the
second argument is a list of the dimensions of the output tensors.  So, for
example, multiplying a 4x5 matrix with a 5-vector to get a 4-vector would be a:

~~~haskell
mulFoo :: TOp '[ '[4, 5], '[5] ]  '[ '[4] ]
~~~

using *DataKinds* to get type-level lists and numerics. (The actual type is
kind-polymorphic on what you use to indicate dimensions)

A simple feed-forward neural network layer might be represented as:

~~~haskell
ffLayer :: TOp '[ '[i], '[o, i], '[o] ] '[ '[o] ]
~~~

Where the layer takes an input `i`-vector, an `o`-by-`i` weights matrix, and an
`o`-vector of biases, and produces an `o`-vector of resuts.

One important thing that makes `TOp`s usable is that they *compose*: that
is, that you can build complex `TOp`s by composing and putting together
smaller, simpler ones.  The `ffLayer` `TOp` above might, for example, be
created by chaining a matrix-vector multiplication, a vector-vector addition,
and an operation that maps the [logistic function][] over every element in a
tensor.

[logistic function]: https://en.wikipedia.org/wiki/Logistic_function

`TOp`s can be "run" on any instance of the [`Tensor`][tensor] typeclass:

~~~haskell
runTOp
    :: Tensor t
    => TOp ns ms
    -> Prod t ns
    -> Prod t ms
~~~

[tensor]: https://mstksg.github.io/tensor-ops/TensorOps-Types.html#t:Tensor

(`Prod f as` is a heterogeneous vinyl-like list, where `Prod f '[a,b,c]`
contains an `f a`, an `f b`, and an `f c`.  So here, it's a collection of
tensors of each of the input dimensions.)

The key to the usefulness of this library is that you can also calculate the
*gradient* of a `TOp`, using reverse-mode tensor-level automatic
differentation:

~~~haskell
gradTOp
    :: Tensor t
    => TOp ns '[ '[] ]     -- result must be single scalar
    -> Prod t ns
    -> Prod t ns
~~~

So, given a `TOp` producing a scalar and collection of input tensors, it
outputs the derivative of the resulting scalar with respect to each of the
input tensors.

If you run it on `ffLayer` and `x`, `w`, and `b` (input, weights, biases) with
a `TOp` producing an error function, it'll output tensors of the same size
as `x`, `w`, and `b`, indicating the direction to move each of them to in to
minimize the error function.  To train the network, you'd step `w` and `b` in
that indicated direction.

Right now the user-facing API is non-existent, and usage requires juggling a
lot of extra singletons for type inference to work.  But hopefully these can be
ironed out in a final version.

Currently, the only way to compose `TOp`s is through their `Category` instance,
and a pseudo-Arrow-like interface:

~~~haskell
-- Compose `TOp`s, from Control.Category
(>>>)
    :: TOp ns ms
    -> TOp ms os
    -> TOp ns os

-- Similar to `first` from Control.Arrow
firstOp
    :: forall os ns ms. ()
    => TOp ns ms
    -> TOp (ns ++ os) (ms ++ os)

-- Similar to `second` from Control.Arrow
secondOp
    :: forall os ns ms. ()
    => TOp ns ms
    -> TOp (os ++ ns) (os ++ ms)
~~~

And so, you can write `ffLayer` above as:

~~~haskell
import           TensorOps.Types
import qualified TensorOps.TOp as TO

ffLayer'
    :: TOp '[ '[i], '[o,i], '[o] ] '[ '[o] ]
ffLayer' = firstOp (TO.swap >>> TO.matVec)
       >>> TO.add
~~~

Where `TO.swap >>> TO.matVec` turns `'[ '[i], '[o,i] ]` into `'[o]` by swapping
and doing a matrix-vector multiplication, and
`TO.add :: TOp '[ '[o], '[o] ] '[ '[o] ]` adds the result with the bias vector.

This is mostly done for now for simplicity in implementation, to avoid having
to worry about representing abstract functions and indexing schemes and stuff
like that.  But, it does make more complex functions a bit of a hassle, so a
more flexible/easy-to-write formulation might be in the future.

Of course, composition is always type-safe (with tensor dimensions), and you
can't compose two actions that don't agree on tensor dimensions.  Yay dependent
types.

There are currently three working instances of `Tensor`:

1.  A nested linked list implementation
2.  A nested vector implementation
3.  An hmatrix implementation (facilitated by nested vectors for ranks > 2)

If you want to write your own by providing basic linear algebra functions, make
your type an instance of the `BLAS` typeclass (which contains the BLAS
interface, plus some helpers) and you get it for free!  See
[`TensorOps.BLAS`][blas] for details and [`TensorOps.BLAS.HMat`][hmat] for an
example implementation.

[blas]: https://mstksg.github.io/tensor-ops/TensorOps-BLAS.html
[hmat]: https://mstksg.github.io/tensor-ops/TensorOps-BLAS-HMat.html

Haddocks are put up and rendered [here][haddocks], but the library is not super
well commented at this point!  Most of the API is in the `TensorOps` top-level
module.

[haddocks]: https://mstksg.github.io/tensor-ops

There are currently two applications just for testing out the features by using
them to implement neural networks: *tensor-ops-dots*, which uses a simple tiny
network for learning a non-linear 2D function with interchangeable backends,
and *tensor-ops-mnist*, which uses a feed-forward neural network w/ the
*hmatrix* backend to classify the ubiquitous [mnist][] data set.  Use with
`--help` for more information.

[mnist]: http://yann.lecun.com/exdb/mnist/
