# `antireduce`

The `antireduce` library offers a suite of generic tools for performing distributional program search and library learning under the assumption that artifacts are maintained within the local file system.  The main goal of the `antireduce` library is to be agnostic to the semantics of the Domain-Specific Library (DSL) of operations that defines a search space over programs.  It is expected that downstream libraries will specialize the basic operations offered by `antireduce` for the particular class of DSLs they support.  For an example of how this may be done, see [`antireduce-graphs`](https://github.com/shlomenu/antireduce-graphs).

Please note that as of now, the compression capabilities offered here require the use of a normal form that is verbose and cumbersome with respect to the current mechanism of distributional search.  This normal form is not required by the STITCH [compression tool](https://pypi.org/project/stitch-core/) which is currently preferred by the project for which this library was designed.  As such, the compression implementation is preserved but is currently incompatible with the use of distributional search.  It is instead expected and encouraged that one use STITCH, a practice made straightforward by the use of the local file system to preserve artifacts.  For an example of how this may be done, see the main [project page](https://github.com/shlomenu/symbolically_synthesized_networks).

## Most Relevant Modules for Downstream OCaml Libraries:

 - `Type`
 - `Program`
 - `Arg_typed_program`
 - `Util`
 - `Parser`
 - `Exploration`

## Most Relevant Modules for Direct Interoperation with Python (Not Requiring Specialization in Downstream Libraries):

 - `Dsl`
 - `Factorization`
 - `Frontier`
 - `Program`
 - `Compression` (Unless using the STITCH compression tool&mdash;recommended)

## Module Reference (Alphabetized)

### `Arg_typed_program`

`Arg_typed_program.t` represents a program in which only De Bruijn indices are annotated with types (see `Typed_program` for a module whose principal type represents fully-annotated programs).  This class of programs is crucial to enabling translation between well-typed values of `Program.t` and compositions of 
native OCaml functions in downstream libraries, as values of `Arg_typed_program.t` may be assigned a type by the compiler in a straightforward manner even when they contain free variables.  Values of `Arg_typed_program.t` are constructed by creating a value of `Typed_program.t` from a value of `Program.t` and a value of `Type.t` characterizing its largest subexpression, then removing type annotations from all subexpressions that are not De Bruijn indices.   

### `Array_list`

Basic resizable arrays.

### `Beam_search`

`Beam_search.t` represents the state of a breadth-limited search for the minimum cost inhabitants of a version space under the assumption that a particular newly-invented primitive is available.  The operations offered by this module utilize the operations of the `Version_and_cost_table` module to minimize the cost of version spaces across unions while selectively aggregating and tracking information on the cost of substituting the novel invention in a variety of subexpressions.  This functionality is used during compression to perform a more resource efficient evaluation of the utility of a body of invented primitives without calculating an exactly optimal rewriting of the frontier for each candidate.

### `Compression`

The `Compression` module offers the `compress` operation, the high-level entry point to `antireduce`'s library learning functionality.  `compress` iteratively extracts invented primitives based on the subexpressions present in a corpus of programs, at each stage selecting the primitive that allows for the greatest reuse within a refactored corpus of programs.  Unlike distributional search, `compress` does not rely on access to the semantics of programs in order to operate, and therefore does not need to be specialize to specific sets of base primitives and their implementations.

### `Cost_table`

`Cost_table.t` represents the state of a search for the minimum cost inhabitants of a version space under the assumption that a particular newly-invented primitive is available.  The `minimal_inhabitant_cost` and `minimal_inhabitant` functions offered by this module recursively minimize the cost of version spaces across unions while tracking the cost of substituting the novel invention in a variety of subexpressions.  Unlike `Version_and_cost_table.minimum_cost_inhabitant`, these functions retain only enough information on the identities of the version spaces involved to find a single minimum cost inhabitant, rather than ordering all inhabitants by their cost.  This functionality is used during compression to find optimal rewritings of frontier programs.

### `Derivation`

`Derivation.t` is a record type representing an abstract syntax tree.  A value of `Derivation.t` is defined by a base or invented primitive, the arguments (subtrees) to which it is applied, its type when fully applied to these arguments, and its log likelihood.  Values of `Derivation.t` are easily converted to values of `Program.t`. 

### `Dsl_entry`

`Dsl_entry.t` is a record type representing a base or invented primitive suitable for inclusion under the `library` attribute of a `Dsl.t`.  All values of `Dsl_entry.t` have two names, a type, a log likelihood, and a value of `Fast_type_unification.t`.  One of these names, given by the attribute `dc_name`, dictates how the primitive is serialized as an anonymous function.  The other name, given by the attribute `stitch_name`, dictates how the primitive is serialized as a named function.  For base primitives, the values of `dc_name` and `stitch_name` are identical; for invented primitives they (typically) differ.  The `impl` attribute provides the definition of a primitive.  For base primitives, no such definition is needed; it is supplied by downstream libraries via native OCaml implementations.  For invented primitives, this definition is simply the value of `Program.t` that gives the appropriate subexpression.   

### `Dsl_unification`

`Dsl_unification.t` is a record type representing the results of a possible unification of a requested type with a DSL primitive in a particular variable and type context.  A value of `Dsl_unification.t` consists of a base or invented primitive, its log likelihood, a list of types of parameters to which this primitive must be applied to satisfy the requested type, and an updated type context.  This module offers operations relevant to producing the list of all valid values of `Dsl_unification.t` that correspond to a particular DSL, type context, variable context, and requested type.  

### `Dsl`

`Dsl.t` is a record type representing a monadic DSL.  A value of `Dsl.t` is characterized by a list of values of `Dsl_entry.t`, the monomorphic type of its monad (state), the log likelihood it assigns to De Bruijn indices, its size (the number of values of `Dsl_entry.t` it contains), and its mass (the number of uses of base primitives contained in all its values of `Dsl_entry.t`).  In addition to other operations of values of `Dsl.t`, this module implements a rescaling operation which recenters the log likelihoods of all the primitives of a DSL around the mean such that total probability mass is preserved but the spread of the values is altered, thereby influencing the breadth/depth of distributional program search.  This can be crucial for preventing DFS-like behavior that can arise from highly skewed distributions over primitives.       

### `Exploration`

The `Exploration` module contains the high-level operations `unikey_explore` and `multikey_explore` that support distributional program search with a frontier maintained on the local file system.  In order to distinguish programs with unique semantics, the `Exploration` module's functions must be able to execute programs and examine their output.  Consequently, `unikey_explore` and `multikey_explore` require a number of parameters related to the execution of programs and the de/serialization and comparison of their outputs.  The `unikey_*` family of functions is intended for use in situations where the outputs of programs admit a total ordering via a comparison function or can be hashed.  The `multikey_*` family of functions is intended for use in circumstances where outputs of program do not admit total ordering or precise hashing, but support equality testing.  In the latter case, a function for extracting both "primary" keys, IDs that don't admit total ordering or unique hashes, as well as "secondary" keys, which admit equality testing 
must be provided.  Collisions between primary keys are then resolved in linear time by testing secondary keys.  As described under `Compression`, distributional search is currently incompatible with compression as offered through this library; it is assumed instead that users will prefer the STITCH compression [tool](https://pypi.org/project/stitch-core/).  In this case, the `Exploration` module is the main entry point to the `antireduce` library, and it is worthwhile to describe the parameters of its two high-level operations in detail:

`unikey_explore` and `multikey_explore`:
 - `exploration_timeout`: time spent enumerating programs; the time needed to evaluate programs is also considered towards this count.  This amount of time will be spent searching regardless of the value of `max_novel_representations`.  If too many novel representations have already been found, then programs will be retained only if they achieve the same semantics as another program in the frontier and are smaller by mass.
 - `max_novel_representations`: the number of programs with outputs not yet in the frontier that are retained and saved during search.  The first `max_novel_representations` programs with such semantics are retained as these are most likely under the heap search algorithm.
 - `program_size_limit`: the maximum number of base or invented primitives a program may contain and be considered for inclusion in the frontier.
 - `eval_timeout`: the amount of time allowed for evaluation of a program after it has been enumerated.
 - `attempts`: the number of times evaluation of a program will be attempted if `eval_timeout` is exceeded.
 - `dsl`: the DSL defining the search space to be explored
 - `representations_dir`: the directory of JSON files considered to contain the current frontier.
 - `apply_to_state`: a function that transforms a program into one that is fully applied and may be reduced to a value of `dsl.state_type`.
 - `evaluate`: a function that transforms an enumerated program's source and type-annotated forms into an optional output.
 - `retrieve_result`: for unimportant reasons, while well-typed values of `Program.t` can be transformed into native OCaml functions and evaluated, there results cannot be accessed within the use of effects.  That is, enumerated programs must trigger the effects necessary to save their result.  These operations are universal and need not be enumerated, and are therefore appropriate to add after the fact via `apply_to_state`.  This parameter provides a function that may be executed to retrieve that result from the location where it was stored as a consequence of running `evaluate` thanks to the operations added by `apply_to_state`.  
 - `nontrivial`: some enumerated programs may be valid but produce trivial outputs.  This function is applied to the output of a function following evaluation to determine whether or not it should be immediately discarded.  
 - `parse`: a dsl-insensitive parsing function
 - `request`: the type of program to be enumerated
 - `yojson_of_output`: serialization function for program outputs
 - `primary_key_modl`: the module needed to parametrize collections by the type of the primary key (supplied as `(module PrimKey)`)

`unikey_explore`:
 - `primary_key_of_output`: extracts a primary key from a program output
 - `yojson_of_primary_key`: serializes a primary key
 - `primary_key_of_yojson`: deserializes a primary key

`multikey_explore`:
 - `keys_of_output`: extracts a tuple of primary key, secondary key from a program's output; provided as one function for circumstances in which the extraction of primary keys and secondary keys rely on the same intermediate computations
 - `yojson_of_primary_key`: serializes a primary key
 - `primary_key_of_yojson`: deserializes a primary key
 - `yojson_of_secondary_key`: serializes a secondary key
 - `secondary_key_of_yojson`: deserializes a secondary key
 - `equal_secondary_key`: performs an equality test between secondary keys

As a consequence of the `*_explore` operations, the contents of the `representations_dir` directory is updated with abbreviations of preexisting programs or novel programs that have been discovered during search.  The JSON files in the `representations_dir` directory contain JSON objects with the following keys:

 - `program`: serialized program in `` `Combined`` format (both the names and definitions of invented primitives are available inline).
 - `stitch_program`: serialized program in `` `Stitch`` format (both base and invented primitives are referred to by name with no inline definition).
 - `size`: the number of base or invented primitives in the program.
 - `mass`: the number of base primitives in the program (including within invented primitives).
 - `output`: the output of executing the program according to the semantics of the base primitives in the DSL.
 - `primary_key`: if `secondary_key` is not present, a key with a total ordering/supporting hashing that represents the program's unique output/semantics; if `secondary_key` is present, a key providing partial ordering/hashing with significant known collisions that somewhat distinguishes the program's unique output/semantics. 
 - `secondary_key`: a key such that equality indicates an exact match between the semantics of two programs by the tightest standard relevant to the application.

### `Factorization`

`Factorization.t` represents a decomposition of a program or body of programs into counts of actual and potential usages of primitives under a given DSL.  This decomposition can be straightforwardly turned into a unigram distribution over primitives summarizing their relative frequencies within the corpus.  The `factorize` function relies on the `Typed_program` module to fully disambiguate the types of all subexpressions, then applies the operations of the `Dsl_unification` module to account for all primitives compatible with each annotation.  The `to_log_likelihood` function turns counts of actual and potential usages of primitives into an estimation of the log likelihood of a program by multiplying them by the log likelihood of their respective primitives under a given DSL.  The `inside_outside` function counts the occurrences of primitives within a corpus of programs, forms a weighted sum of these counts according to the likelihood of each program under a given DSL, and produces a reweighted DSL according to the resulting unigram distribution.  If the parameters of the DSL supplied to `inside_outside` place uniform probability on all primitives, the distribution given by the reweighted DSL will purely reflect the frequency of primitives within this corpus. 

### `Fast_type_unification`

`Fast_type_unification.t` represents a stateful procedure for unifying a type with a given, fixed type signature.  `Fast_type_unification.t` is a record type with fields corresponding to a value of `Fast_type.t`,
its corresponding array of pointers, and a unification function specialized to a specific type signature.  The use of this unification function modifies the state of the array of pointers, which can be seen by examining the value of `Fast_type.t` (mainly for debugging purposes).  The unification function created by `Fast_type_unification.of_type` returns a list of type contexts and parameter lists; each parameter list provides the types to which a base primitive must be applied to unify with the requested type.  In the event that there are multiple bindings that achieve this, all will be returned.

### `Fast_type`

`Fast_type.t` represents a polymorphic type consisting of an arrow, constructor, or numeric type identifier.  `Fast_type.t` differs from `Type.t` in that it uses a dedicated array of pointers to map numeric type identifiers to types as needed to perform unification for a particular type signature.  This is intended to facilitate faster unification for type signatures which are commonly encountered, such as those of base primitives.

### `Frontier`

The `Frontier` module contains utilities for managing a frontier of programs stored as JSON files in the local file system.  These JSON files are assumed to be created via functions in the `Exploration` module.  The `load_representations` function takes a directory, a parsing function, and a list of JSON files, and produces a corresponding list of programs, paths, and JSON objects.  Given an alternative aligned list of shorter replacement programs, `overwrite_representations` can be used to remove the JSON file at each path create a new JSON file at a new path each updated to reflect the replacement program.  This is necessary because MD5 hashes of programs are used to determine the names of files and are stored within the contents of those files.  Therefore both their contents and their location must be updated when a shorter program is found that produces the same output.     

### `Heap_search`

`Heap_search.t` represents the state of a run of the heap search algorithm.  This state contains a mapping from each type of reachable subexpression to the heap, successor relation, and set of previously encountered derivations needed to maintain and index the search frontier associated with that type.  A value of `Heap_search.t` may be initialized from any value of `Pcfg.t`.  This state `s` may be used with `query` and a derivation `deriv_cur` to produce the next most likely derivation `deriv_next` and a new state `s'`, functionally updated to maintain the invariants necessary to call `query` recursively on `s'` and `deriv_next`.  

### `Parser`

The `Parser` module contains functions for deserializing type signatures, and values of `Program.t` that have been serialized either in `` `Stitch`` or `` `Combined`` format.  When reading programs in `` `Combined`` format, no DSL is necessary as both the names and definitions of invented primitives are available within the program.  When reading programs in `` `Stitch`` format, only named primitives are used, so a reference DSL is necessary and names not recognized under that DSL, if encountered, will raise an `Unparseable` exception.  This is adequate as all programs written by functions in the `Exploration` module are in `` `Combined`` format, and the definitions of new STITCH-invented primitives are in `` `Stitch`` format; they simply must be incorporated into the DSL iteratively so that definitions do not reference unbound primitives. 

### `Partial_derivation`

`Partial_derivation.t` is a record type representing an individual result of a search over the space of derivations reachable under a given DSL.  This search is limited, and produces a "partial" result, because it ends as soon as a type is encountered such that matching derivations cannot lead to the discovery of novel rules.  There are several mechanisms to detect these redundant parts of the search space built into the operation `find`: (a) types which already have productions in the grammar are not expanded to form partial derivations (except for the type given by the start symbol); (b) an individual partial derivation cannot contain multiple expansions of the same type (to prevent looping recursion); (c) an individual partial derivation cannot contain the same transition (triple of function, parameter position, and argument) multiple times.  Since there are a finite number of transitions for any DSL, the last condition guarantees that `find` terminates.  In addition, `find` also places a limit on the size of type for which derivation will be attempted, as unification between some types can lead to type signatures of ever increasing and unbounded size.  Since in such cases transitions would necessarily be repeated, though their equivalent productions would be associated with different types, this suggests that `find` cannot&mdash;in a single call&mdash;account for all productions associated with each valid transition.  For this reason, `find` is meant to be called iteratively, each time returning a list of partial derivations and the type contexts needed to monomorphize all types therein.  Within a subroutine of `Pcfg.of_dsl`, `find` is called iteratively and this monomorphization is done to yield a set of new, monomorphic productions.  The full set of types which have now have productions in the grammer is then accounted for before `find` is called at the next iteration.       

### `Pcfg`

The heap search algorithm retains the optimality of A* but improves on its efficiency by maintaining separate frontiers of the search space for each type of subexpression that may be encountered during program search.  To support this, it is helpful to preprocess the primitives of a DSL and their types into a set of rules about which primitives may be (recursively) enumerated to satisfy each possible monomorphic type.  `Pcfg.t` is a record type representing these rules, given as a mapping from values of `Type.t` to values of `Production.t`.  Values of `Pcfg.t` also indicate the start symbol (the desired type of programs to be enumerated during search), and contain a mapping `max_prob` indicating the most likely production for each type.  The `Pcfg.of_dsl` function produces a value of `Pcfg.t` from a value of `Dsl.t` by repeatedly exploring the search space over programs for new productions using functionality from the `Partial_derivation` module, then determining the maximum probability production for each type from the resulting rules.       

### `Production`

`Production.t` is a record type representing a single node of an abstract syntax tree.  These nodes are defined by a base or invented primitive, its log likelihood, and the types of the arguments to which it is to be applied.

### `Program`

`Program.t` represents a program consisting of De Bruijn indices, lambda abstractions, applications, base primitives and invented primitives.  This module also contains non-stateful functions that directly transform values of type `Program.t`.  Values of `Program.t` are not guaranteed to correspond to well-typed OCaml programs.  This guarantee must be made with respect to the operations that recursively compose values of type `Program.t` during program search.

### `Structural_type`

`Structural_type.t` represents a value of `Type.t` equipped with asymmetric, unification-based equality and comparison.  These operations are made possible by the inclusion of an optional type context.  When this type context is present, equality and comparison are performed after unification/application of the type context to the two operands.  It is assumed that when comparing two values of `Structural_type.t`, that one or zero type contexts are present; if a type context is present, it is expected on the first argument of the equality/comparison function.  This assumption allows the `Structural_type` module to parametrize a set.  Before a value of `Structural_type.t` is added to a set, its type context, if present, is assumed to be applied and discarded so that only unbound type variables remain.  Other values of `Structural_type.t` may then be compared for membership in the set in conjunction with their type context with the knowledge that appropriate unification/application of the context will be performed.  This assumes that all type contexts used in conjunction with set, amongst existing members and values of `Structural_type.t` being tested for comparison, contain compatible bindings.  This requirement is met in the case where all values of `Structural_type.t` in question belong to the same derivation, which by definition permits a consistent set of bindings amongst all type variables at all levels of the expression.  Sets of values of `Structural_type.t` are used under exactly this assumption in the `Partial_derivation` module. 

### `Type_context`

`Type_context.t` represents a functional mapping from numeric type identifiers to `Type.t`s.  An integer may be bound to a value `ty : Type.t` to record that the type identifier may be replaced with `ty` in any type expression according to the current context.  A numeric type identifier may also be created which has no corresponding type in the current context.  The `instantiate` operation maps a type `ty` and a type context `cxt` to a new type `ty'` and type context `cxt'` such that the all numeric type identifiers in `ty` correspond to new unbound type identifiers in `ty'` under `cxt'`.  The `apply` operation maps a type `ty` and type context `cxt` to a new type `ty'` and type context `cxt'` such that all bound type identifiers in `ty` correspond to types in `ty'` consistent with the mapping of `cxt`.  Moreover, if any relevant bindings in `cxt` are indirect in the sense that type identifier `i` is bound to type identifier `j` which is bound to `ty`, in `cxt'` both `i` and `j` will be bound directly to `ty`.     

### `Type_unification`

Implements unification of types within a type context.  The unification operations are exception based, raising a `UnificationError` if unification cannot be performed.

### `Type`

`Type.t` represents a polymorphic type consisting of an arrow, constructor, or numeric type identifier.  This module also contains non-stateful functions that directly transform values of type `Type.t`.  Equality and comparison on values of `Type.t` do not take into account structural equivalences between types that may occur in particular contexts, but rather rely on strict identity between constructor names and the numeric values of type identifiers.

### `Typed_program`

`Typed_program.t` represents a program in which all subexpressions are exhaustively annotated with types (values of `Type.t`).  A `Typed_program.t` consists of De Bruijn indices, lambda abstractions, applications, and base primitives only.  Typed programs are used in the process of proving to the OCaml compiler that instances of `Program.t` correspond to well-typed OCaml programs, which must be managed by downstream libraries with knowledge of the native OCaml implementations of an appropriate set of base primitives.  For this purpose, invented primitives must be eliminated and reduced to base primitives and thus are not represented among the variants of `Typed_program.t`.  This module contains specialized operations for unification, application of a type context, and instantiation.  The most unique among these is the instantiation operation, which must create a proper set of constraints among the types of subexpressions without relying on knowledge of the type of superexpressions. 

### `Util`

General utilities.  Currently contain functions related to timing, timed execution of effectful functions, randomization, mathematical operations, and list- and option-related utility functions.

### `Version_and_cost_table`

`Version_and_cost_table.t` represents the state of a search for the minimum cost inhabitants of a version space under the assumption that a particular newly-invented primitive is available.  The `minimum_cost_inhabitants` function offered by this module recursively minimizes the cost of version spaces across unions while tracking the cost of substituting the novel invention in a variety of subexpressions.  This functionality is used during beam search.

### `Version_space`

`Version_space.t` represents a space of versions of values of `Program.t`.  Values of `Version_space.t` are agnostic to the definitions and type signatures of base and invented primitives.

### `Version_table`

`Version_table.t` represents an efficient hash-cons'd collection of version spaces necessary to represent a corpus of programs.  Values of `Version_table.t` support the calculation of n-step beta inversions for programs that have been incorporated into the table.  Note that after n-step beta inversions are calculated, both version spaces corresponding to refactored programs and version spaces corresponding to unrefactored programs remain in the table.  Since only refactored programs contain unions&mdash;the variant of `Version_space.t` that allows a space to contain more than one member&mdash;tables are therefore always guaranteed to contain a version space with only one member for each program that was incorporated prior to refactoring.  When extracting the set of programs corresponding to a version space known to represent an original, unrefactored program, `extract_program` offers the precise semantics expected of this operation (returning one and only one underlying program).  Otherwise, the more general `extract` operation may be used. 

### `Yojson_util`

Conversions for `Core` maps and hashtables to and from `Yojson.Safe.t` and additional `Yojson`-related utility functions.  

## Acknowledgements

The code in this repository is heavily influenced by the structure and content of the artifacts of the [DreamCoder system](https://github.com/ellisk42/ec) and the artifacts of Fijaelkow et al.'s work on [distributional search](https://github.com/nathanael-fijalkow/DeepSynth).