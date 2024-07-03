# DBM Algorithm and Data Structures Verified using Creusot

## What is this?

This repository contains the implementation of the [DBM (Differential Bound Matrix)](https://en.wikipedia.org/wiki/Difference_bound_matrix) algorithm and its associated data structures in Rust. The DBM algorithm is widely used for time constraint management in real-time system. To enhance robustness, these implementations have been formally verified using [Creusot](https://github.com/creusot-rs/creusot). 

## What Properties are Verified?

We have verified the following properties for each DBM operation:

* Changes on these operations
* Preservation of canonicity in these operations

## DBM Operations

### Implemented and Formally Verified Features

* `up`
* `down`
* `free`
* `reset`

### Not Implemented Features

* `shift`
* `and`
* etc...

## Getting Started

To use this repository, you will need to have [Creusot](https://github.com/creusot-rs/creusot) installed on your machine. If you haven't installed it yet, refer to the [README.md](https://github.com/creusot-rs/creusot?tab=readme-ov-file#installing-creusot-as-a-user) in the official repository.

Next, clone this repository and then move into to the dbm-creusot directory:

```
$ git clone https://github.com/ruth561/VerifiedDBM.git
$ cd dbm-creusot
```

Copy the rust-toolchain file from the Creusot repository to this repository:

```
$ cp /path/to/creusot/rust-toolchain ./
```

To link this repository with Creusot, replace the following dependency in `Cargo.toml`:

```toml
...
[dependencies]
creusot-contracts = { path = "/path/to/creusot/creusot-contracts" }
...
```

Now, all necessary procedures are completed! To perform proofs for each DBM operation, please execute the following command:

```
$ cargo creusot why3 ide
```

## Overview of the Repository

All implementations for DBM operations are contained within the `src/` directory. We have implemented each DBM operation in separate files. For example, the `down` operation is implemented in the `src/down.rs` file.

## Future Works

Although we have implemented these features in a simplified manner to ensure successful verification, more accurate implementations are needed for practical use. Future implementations should include:

* Distinguishing between `(<, m)` and `(<=, m)`
* $k\text{-Normalization}$
* $k,\mathcal{G}\text{-Normalization}$
