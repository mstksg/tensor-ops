tensor-ops
==========

[![Build Status](https://travis-ci.org/mstksg/tensor-ops.svg?branch=master)](https://travis-ci.org/mstksg/tensor-ops)

Adding a quick readme because of a recent explosion in publicity :)

*tensor-ops* is a library for specifying type-safe tensor manipulations that
can be automatically differentiated using reverse-mode AD for automatic
gradient descenet.

The center of everything is a GADT that represents a tensor operation:

~~~haskell
TensorOp :: [k] -> [k] -> Type
~~~

The first argument is a list of the input tensors and their dimensions, and the
second argument is a list of the output tensors and their dimensions.  So, for
example, multiplying a 4x5 matrix with a 5-vector to get a 4-vector would be a:

~~~haskell
mulFoo :: TensorOp '[ '[4, 5], '[5] ]  '[ '[4] ]
~~~

using *DataKinds* to get type-level lists and numerics. (The actual type is
kind-polymorphic on what you use to indicate dimensions)

A simple feed-forward neural network layer might be represented as:

~~~haskell
ffLayer :: TensorOp '[ '[i], '[o, i], '[o] ] '[ '[o] ]
~~~

Where the layer takes an input `i`-vector, an `o`-by-`i` weights matrix, and an
`o`-vector of biases, and produces an `o`-vector of resuts.

One important thing that makes `TensorOp`s usable is that they *compose*: that
is, that you can build complex `TensorOp`s by composing and putting together
smaller, simpler ones.  The `ffLayer` `TensorOp` above might, for example, be
created by chaining a matrix-vector multiplication, a vector-vector addition,
and an operation that maps the [logistic function][] over every element in a
tensor.

[logistic function]: https://en.wikipedia.org/wiki/Logistic_function

`TensorOp`s can be "run" on any instance of the `Tensor` typeclass:

~~~haskell
runTensorOp
    :: Tensor t
    => TensorOp ns ms
    -> Prod t ns
    -> Prod t ms
~~~

(`Prod f as` is a heterogeneous vinyl-like list, where `Prod f '[a,b,c]`
contains an `f a`, an `f b`, and an `f c`.  So here, it's a collection of
tensors of each of the input dimensions.)

The key to the usefulness of this library is that you can also calculate the
*gradient* of a `TensorOp`, using reverse-mode tensor-level automatic
differentation:

~~~haskell
gradTensorOp
    :: Tensor t
    => TensorOp ns '[ '[] ]     -- result must be single scalar
    -> Prod t ns
    -> Prod t ns
~~~

So, given a `TensorOp` producing a scalar and collection of input tensors, it
outputs the derivative of the resulting scalar with respect to each of the
input tensors.

If you run it on `ffLayer` and `x`, `w`, and `b` (input, weights, biases) with
a `TensorOp` producing an error function, it'll output tensors of the same size
as `x`, `w`, and `b`, indicating the direction to move each of them to in to
minimize the error function.  To train the network, you'd step `w` and `b` in
that indicated direction.

Right now the user-facing API is non-existent, and usage requires juggling a
lot of extra singletons for type inference to work.  But hopefully these can be
ironed out in a final version.

Currently, "composition" of `TensorOp`s is [stack-based][]/[concatenative][].
Each tensor operation composes by performing the action on the top of a stack.
`ffLayer` above might be implemented as `mulMatVec >> add >> map logistic`.
This was done for simplicity, to avoid having to worry about representing
abstract functions and indexing schemes and stuff like that.  It's limiting,
but I haven't run into any issues so far, so I might just stick with it for
now.  Of course, composition is always type-safe (with tensor dimensions), and
you can't compose two actions that don't agree on tensor dimensions.  Yay
dependent types.

For now, the only back-end (instances of `Tensor`) is a instance that is
basically nested linked lists with lengths in their types.  Will eventually
have *hmatrix* backends, maybe. Hopefully eventually some day I can make the
API clear enough so people can implement their own backends in libraries like
*accelerate*.

[stack-based]: https://en.wikipedia.org/wiki/Stack-oriented_programming_language
[concatenative]: https://en.wikipedia.org/wiki/Concatenative_programming_language

