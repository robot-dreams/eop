## Loose Ends

3.1: Prove that for an associative operation, all possible parentheses groupings are equivalent
Footnote 3.3 (page 34)
Footnote 4.4 (page 55)
Exercise 4.5: Prove that my solution performs 5 2/3 comparisons on average
Exercise 4.6: My solution is really sloppy

## Questions

What would it look like for a programming language to distinguish value types from object types?
How can we tell when a given finite set of procedures actually forms a computational basis for a type?
What does it mean to have a concept defined on more than one type?  What's an example of such a concept?
How would you formally define the "action" concept?
When would a transformation be more efficient than an action?
Footnote 3.6 (page 42): How would you write such an identity_element function?
What's an example of an optimization that can be made for non-regular functions / types?
Is the difficulty of order-selection with order 5 somehow related to the insolubility of quintics?

## Definitions

### 1.1

An **abstract entity** is an individual thing that is eternal and unchangeable
A **concrete entity** is an individual thing that comes into and out of existence in space and time
An **attribute** is a correspondence between a concrete entity and an abstract entity that describes some property, measurement, or quality of the concrete entity
**Identity** determines the sameness of a thing changing over time
A **snapshot** (of a concrete entity) is a complete collection of its attributes at a particular point in time
An **abstract species** describes common properties of essentially equivalent abstract entities
A **concrete species** describes the set of attributes of essentially equivalent concrete entities
A **function** is a rule that associates one or more abstract entities, called **arguments** (from corresponding species) with an abstract entity, called the **result**, from another species
An **abstract (or concrete) genus** describes different abstract (or concrete) species that are similar in some respect

### 1.2

A **datum** is a finite sequence of 0s and 1s
A **value type** is a correspondence between a species (abstract or concrete) and a set of datums
  A datum corresponding to a particular entity is called a **representation** of the entity (we say the datum **represents** the entity)
  An entity corresponding to a particular datum is called an **interpretation** of the datum
  A **value** is a datum (which we sometimes refer to as the representation of the value; we also sometimes say that the datum represents the value) together with the datum's interpretation (which we sometimes refer to as the interpretation of the value; we also sometimes say that the value represents its datum's interpretation)
    [When we say value, we may be referring to the actual value (i.e. the datum together with its interpretation), only the datum, or only the interpretation; the usage should (hopefully) be clear from context]
A datum is **well-formed** (with respect to a value type) if that datum represents an abstract entity
A value type is **properly partial** if its values represent a proper subset of the abstract entities in the corresponding species; otherwise it is **total**
A value type is **uniquely represented** if at most one value corresponds to each abstract entity
A value type is **ambiguous** if a datum has more than one interpretation; otherwise, it is **unambiguous**
Two values of a value type are **equal** if they represent the same abstract identity (i.e. if they have the same interpretation)
Two values of a value type are **representationally equal** if their datums are identical sequences of 0s and 1s
A function defined on a value type is **regular** if substituting an equal value for an argument gives an equal result

### 1.3

A **memory** is a set of words, each with an **address** and a **content**
  The addresses are values of a fixed size, called the **address length**
  The contents are values of another fixed size, called the **word length**
  The content of an address is obtained by a **load** operation
  The association of a content with an address is changed by a **store** operation
An **object** is a representation of an entity as a value in memory
  An object has a **state** that is a value of some value type
    The state is changeable
    The state corresponds to a snapshot of the concrete entity corresponding to the object
  An object owns a set of **resources** (memory, file) to hold its state
  An object (for the purposes of this book) has a unique **starting address** from which all of its resources can be reached
An **object type** is a pattern for storing and modifying values in memory
An object is {well-formed, properly partial, total, uniquely represented} if its state is {well-formed, properly partial, total, uniquely represented}
  Each object type has a corresponding value type describing states of objects of that type
An **identity token** is a value expressing the identity of an object, and is computed from the value of the object and the address of its resources
  Testing equality of identity tokens corresponds to testing equality of identity
Two objects of the same type are equal if their states are equal
  If two objects are equal, and the two objects do not have equal identity tokens, then we say that one is a **copy** of the other
  Making a change to an object does not affect any copy of it
When we say type (without qualification), we mean object type

### 1.4

A **procedure** is a sequence of instructions that modifies the state of some objects; it may also construct or destroy objects
Procedures interact with four different kinds of objects:
  1. Input/output: objects passed to/from a procedure directly or indirectly through its arguments or returned result
  2. Local state: objects created, destroyed, and usually modified during a single invocation of the procedure
  3. Global state: objects accessible to this and other procedures across multiple invocations
  4. Own state: objects accessible only to this procedure (and its affiliated procedures) but shared across multiple invocations
An object is passed **directly** if it is passed as an argument or returned as a result
An object is passed **indirectly** if it is passed by a pointer or a pointerlike object
An object is an **input** to a procedure if it is read, but not modified, by a procedure
An object is an **output** from a procedure if it is written, created, or destroyed by the procedure, but its initial state is not read by the procedure
An object is an **input/output** of a procedure if it is modified as well as read by the procedure
A **computational basis** for a type is a finite set of procedures that enable the construction of any other procedure on the type
  A basis is **efficient** if any proceduer implemented using it is as [asymptotically] efficient as an equivalent procedure written in terms of an alternative basis
  A basis is **expressive** if it allows compact and convenient definitions of procedures on the type

### 1.5

A type is **regular** if its basis includes equality, assignment, destructor, default constructor, copy constructor, total ordering, and underlying type
**Equality** is a procedure that takes two objects of the same types and returns true if and only if the object states are equal (inequality is the negation of equality)
**Assignment** is a procedure that takes two objects of the same type and makes the first object equal to the second without modifying the second; the meaning of assignment does not depend on the initial value of the first object
A **destructor** is a procedure causing the cessation of an object's existence
A **constructor** is a procedure transforming memory locations into an object
An object is in a **partially formed** state if it can be assigned to or destroyed
A **default constructor** is a constructor that takes no arguments and leaves the object in a partially formed state
A **copy constructor** for a type is a constructor that takes an argument of the same type and constructs a new object equal to the argument

### 1.6

A procedure is **regular** if replacing its inputs with equal objects results in equal output objects
A **functional procedure** is a regular procedure defined on regular types, with one or more direct inputs and a single output that is returned as a result of the procedure
  Note that we can pass inputs either by value (making a local copy) or by constant reference
  A functional procedure can be implemented as a C++ function, function pointer, or functor (function object)
The **definition space** for a functional procedure is the subset of values for tis inputs to which it is intended to be applied
  A functional procedure always terminates on input in its definition space
A **homogeneous** functional procedure is one whose input objects are all the same type
The **domain** of a homogeneous functional procedure is the type of its inputs
The **codomain** for a functional procedure is the type of its output
The **result space** for a functional procedure is the set of all values from its codomain returned by the procedure for inputs from its definition space

### 1.7

A **concept** is a collection of requirements (expressed as syntactic and semantic properties) on types
  Type represents species; concepts represent genera
A **type attribute** is a mapping from a type to a value describing some characteristic of the type
A **type function** is a mapping from a type to an affiliated type
  An indexed type function takes an additional constant integer parameter
A **type constructor** is a mechanism for creating a new type from one or more existing types
More formally, a **concept** is a description of requirements on one or more types stated in terms of the existence and properties of procedures, type attributes, and type functions defined on the types
We say a concept is **modeled by** specific types, or that the types **model** the concept, if the requirements are satisfied for those types
A concept C' **refines** another concept C if whenever C' is satisfied for a set of types, C is also satisfied for that set of types
A concept C **weakens** another concept C' if C' refines C
A **type concept** is a concept defined on one type
We define a concept C by writing

        C(T_0, ..., T_{n-1}) := E_0 ^ E_1 ^ ... ^ E^{k-1}

  The T_i are formal type parameters
  Each E_i is a concept clause that takes one of three forms:
    1. Application of a previously defined concept, indicating a subset of the formal type parameters that model it
    2. Signature of a type attribute, type function, or procedure that must exist for any types modeling the concept
        A procedure signature takes the form f: T -> T', where T is the domain and T' is the codomain
        A type function signature takes the form F: C -> C', where the domain and codomain are concepts
    3. Axiom expressed in terms of these type attributes, type functions, and procedures
  We sometimes include the definition of a type attribute, type function, or procedure following its signature in the second kind of concept clause, though particular models may override this definition

        UnaryFunction(F) :=
            FunctionalProcedure(F)
          ^ Arity(F) = 1
          ^ Domain: UnaryFunction -> Regular
                F |-> InputType(F, 0)

        HomogeneousFunction(F) :=
            FunctionalProcedure(F)
          ^ Arity(F) > 0
          ^ (forall i, j in N)(i, j < Arity(F)) => (InputType(F, i) = InputType(F, j))
          ^ Domain: HomogeneousFunction -> Regular
                F |-> InputType(F, 0)

An **abstract** procedure is parametrized by types and constant values, with requirements on those parameters
  An abstract procedure is regular if all its instantiations are regular
**Preconditions** describe properties of particular objects

### 2.1

    Predicate(P) :=
        FunctionalProcedure(P)
      ^ Codomain(P) = bool

    HomogeneousPredicate(P) :=
        Predicate(P)
      ^ HomogeneousFunction(P)

    UnaryPredicate(P) :=
        Predicate(P)
      ^ UnaryFunction(P)

    Operation(Op) :=
        HomogeneousFunction(Op)
      ^ Codomain(Op) = Domain(Op)

A procedure is **partial** if its definition space is a subset of the direct product of the types of its inputs
A procedure is **total** if its definition space is equal to the direct product of the types of its inputs (we consider a total function to be partial)
A procedure is **nontotal** if it is partial but not total
A **definition-space predicate** for a partial procedure f is a [total] predicate p, with the same input types as f, that returns true if and only if the inputs are within the definition space of f

    Transformation(F) :=
        Operation(F)
      ^ UnaryFunction(F)
      ^ DistanceType: Transformation -> Integer

When f is a transformation, we define its powers as follows:

    f^n(x) = | x              if n = 0
             | f^{n-1}(f(x))  if n > 0

### 2.2

y is **reachable** from x under a transformation f if for some n >= 0, y = f^n(x)
x is **cyclic** under f if for some n >= 1, x = f^n(x)
x is **terminal** under f if x is not in the definition space of f
The **orbit** of x under a transformation f is the set of all elements reachable from x under f
If y is reachable from x under f, the **distance** from x to y is the smallest non-negative integer n such that f^n(x) = y
Given a transformation type F, DistanceType(F) is an integer type large enough to encode the distance between any two elements of Domain(F)
An orbit of x under a transformation is:
  **infinite**      if it has no cyclic or terminal elements (otherwise, it is **finite**)
  **terminating**   if it has a terminal element
  **circular**      if x is cyclic
  **p-shaped**      if x is not cyclic, but its orbit contains a cyclic element
The **orbit cycle** is the set of cyclic elements in the orbit (empty for infinite orbits and terminating orbits)
The **orbit handle** is the complement of the orbit cycle with respect to the orbit (empty for circular orbits)
The **connection point** is the first cyclic element (i.e. f^n(x) where n is the smallest non-negative integer such that f^n(x) is cyclic under f)
  The connection point of a circular orbit is the first element
  The connection point of a p-shaped orbit is the first element after the handle
  Infinite orbits and terminating orbits do not have a connection point
The **orbit size (o)** of an orbit is the number of distinct elements in the orbit
The **handle size (h)** of an orbit is the number of elements in the orbit handle
The **cycle size (c)** of an orbit is the number of elements in the orbit cycle

### 2.3

The **collision point** of a transformation f and a starting point x is the unique y such that y = f^n(x) = f^{2n+1}(x), and n >= 0 is the smallest integer satisfying this condition

### 2.5

An **action** is a procedure that changes the state of an object

### Chapter 3

    BinaryOperation(Op) :=
        Operation(Op)
      ^ Arity(Op) = 2

If f and g are transformations on the same domain, their **composition**, g o f, is a transformation mapping x to g(f(x))
An element x has **finite order** under an associative operation if there exist integers 0 < n < m such that x^n = x^m
An element x is an **idempotent element** under an associative operation if x = x^2

**Theorem 3.1.** An element of finite order has an idempotent power.
**Proof.** Suppose x has finite order, i.e. x^n = x^m for integers 0 < n < m.  Let f be the transformation that maps y to xy; then the orbit of x under f contains the cyclic element x^n (since f^{m-n}(x^n) = x^{m-n} * x^n = x^m = x^n).  Then

    x^{n*(m-n)}^2 = x^{n*(m-n)} * x^n * x^{n*(m-n-1)}
                  = f^{n*(m-n)}(x^n) * x^{n*(m-n-1)}
                  = x^n * x^{n*(m-n-1)}
                  = x^{n*(m-n)}

which shows that x^{n*(m-n)} is idempotent.

**Proof.** (EoP) Suppose x has finite order, and let f be the transformation that maps z to xz.  Then the orbit of x under f has a cyclic element.  Let y = f^n(x) be the collision point of f and x; then f^n(x) = f^{2n+1}(x), and by the definition of f, x^{n+1} = x^{2n+2}, which shows that x^{n+1} is idempotent.

A recursive procedure is in **tail-recursive form** if the procedure's execution ends with the recursive call
A recursive procedure is in **strict tail-recursive form** if all the tail-recursive calls are done with the formal parameters of the procedure being the corresponding arguments
Using an operator symbol or procedure name with the same semantics on different types is called **overloading**
  In this case, we say that the operator symbol or procedure name is **overloaded** on the type
A **linear recurrence function of order k** is a function f such that

    f(y_0, ..., y_{k-1}) = \Sum_{i=0}^{k-1} a_i y_i, where a_0, a_{k-1} != 0

A sequence is a **linear recurrence of order k** if there is a linear recurrence function of order k--say f--and

    (forall n >= k) x_n = f(x_{n-1}, ..., x_{n-k})

Changing the state of an object by combining it with another object via a binary operation defines an **accumulation procedure** on the object
An algorithm is **abstract** if it can be used with different models satisfying the same requirements (eg. associativity)

## Chapter 4

A [binary] **relation** is a predicate taking two parameters of the same type:

    Relation(Op) :=
        HomogeneousPredicate(Op)
      ^ Arity(Op) = 2

A relation is **transitive** if whenever it holds between a and b, and between b and c, it holds between a and c

    property(R: relation)
    transitive: R
        r |-> (forall a, b, c in Domain(R)) (r(a, b) ^ r(b, c) implies r(a, c))

A relation is **strict** if it never holds between an element and itself
A relation is **reflexive** if it always holds between an element and itself

    property(R: relation)
    strict: R
        r |-> (forall a in Domain(R)) !r(a, a)

    property(R: relation)
    reflexive: R
        r |-> (forall a in Domain(R)) r(a, a)

A relation is **symmetric** if whenever it holds in one direction, it holds in the other
A relation is **asymmetric** if it never holds in both directions

    property(R: relation)
    symmetric: R
        r |-> (forall a, b in Domain(R)) (r(a, b) implies r(b, a))

    property(R: relation)
    asymmetric: R
        r |-> (forall a, b in Domain(R)) (r(a, b) implies !r(b, a))

Given a relation r(a, b), we define the following **derived relations** with the same domain:

                complement_r(a, b) <=> !r(a, b)
                  converse_r(a, b) <=> r(b, a)
    complement_of_converse_r(a, b) <=> !r(b, a)

A relation is an **equivalence** if it is transitive, reflexive, and symmetric

    property(R: relation)
    equivalence: R
        r |-> transitive(r) ^ reflexive(r) ^ symmetric(r)

An **equivalence class** for an equivalence relation is a subset of its domain containing all elements equivalent to a given element
We can implement an equivalence relation by defining a **key function**, a function that returns the same value for all elements in a given equivalence class (and different values for elements in different equivalence classes)

    property(F: UnaryFunction, R: Relation)
        requires(Domain(F) = Domain(R))
    key_function: F x R
        (f, r) |-> (forall a, b in Domain(F)) (r(a, b) <=> f(a) = f(b))

A relation is a **total ordering** if it is transitive and obeys the **trichotomy law** (for every pair of elements, exactly one of the following holds: the relation, its converse, or equality)

    property(R: Relation)
    total_ordering: R
        r |-> transitive(r) ^
              (forall a, b in Domain(R)) exactly one of the following holds:
                  r(a, b), r(b, a), or a = b

A relation is a **weak ordering** if it is transitive and there is an equivalence relation on the same domain such that the original relation obeys the **weak-trichotomy law** (for every pair of elements, exactly one of the following holds: the relation, its converse, or the equivalence relation)

    property(R: Relation, E: Relation)
        requires(Domain(R) = Domain(E))
    weak_ordering: R
        r |-> transitive(r) ^ (exists e in E) equivalence(e) ^
              (forall a, b in Domain(R)) exactly one of the following holds:
                  r(a, b), r(b, a), or e(a, b)

Given a relation r, the relation !r(a, b) ^ !r(b, a) is called the **symmetric complement** of r
Given a key function f on a set T, together with a total ordering r on the codomain of f, we can define the following weak ordering on T:

    r'(x, y) <=> r(f(x), f(y))

We refer to total and weak orderings as **linear orderings**
An algorithm is **stable** if it respects the original order of equivalent objects

    TotallyOrdered(T) :=
        Regular(T)
      ^ <: T x T -> bool
      ^ total_ordering(<)

## Chapter 5

An element is called an **identity element** of a binary operation if, when combined with any other element as the first or second element, the operation returns the other element:

    property(T: Regular, Op: BinaryOperation)
        requires(T = Domain(Op))
    identity_element: T x Op
        (e, op) |-> (forall a in T) op(a, e) = op(e, a) = a

A transformation is called an **inverse operation** of a binary operation with respect to a given element (usually the identity of the binary operation) if it satisfies the following:

    property(F: Transformation, T: Regular, Op: BinaryOperation)
        requires(Domain(F) = T = Domain(Op))
    inverse_operation: F x T x Op
        (inv, e, op) |-> (forall a in T) op(a, inv(a)) = op(inv(a), a) = e

A binary operation is **commutative** if its result is the same when its arguments are interchanged:

    property(Op: BinaryOperation)
    commutative: Op
        op |-> (forall a, b in Domain(Op)) op(a, b) = op(b, a)

A set with an associative operation is called a **semigroup**
A type with + (which should be commutative) is called an **additive semigroup**

    AdditiveSemigroup(T) :=
        Regular(T)
      ^ +: T x T -> T
      ^ associative(+)
      ^ commutative(+)

A type with * (which is not necessarily commutative) is called a **multiplicative semigroup**

    MultiplicativeSemigroup(T) :=
        Regular(T)
      ^ *: T x T -> T
      ^ associative(*)

A semigroup with an identity element is called a **monoid**
We denote the additive identity element by 0, and define an **additive monoid** as follows:

    AdditiveMonoid(T) :=
        AdditiveSemigroup(T)
      ^ 0 in T
      ^ identity_element(0, +)

We denote the multiplicative identity element by 1, and define a **multiplicative monoid** as follows:

    MultiplicativeMonoid(T) :=
        MultiplicativeSemigroup(T)
      ^ 1 in T
      ^ identity_element(1, *)

A monoid with an inverse operation is called a **group**
We denote the inverse operation of an additive monoid by -, and define an **additive group** as follows:

    AdditiveGroup(T) :=
        AdditiveMonoid(T)
      ^ -: T -> T
      ^ InverseOperation(unary -, 0, +)
      ^ -: T x T -> T
            (a, b) |-> a + (-b)

Similarly, we define a **multiplicative group** as follows:

    MultiplicativeGroup(T) :=
        MultiplicativeMonoid(T)
      ^ multiplicative_inverse: T -> T
      ^ InverseOperation(multiplicative_inverse, 1, *)
      ^ /: T x T -> T
            (a, b) |-> a * multiplicative_inverse(b)

We write multiplicative_inverse(x) as x^{-1}
When both + and * are present on a type, they are [i.e. should be] interrelated with axioms defining a **semiring**:

    Semiring(T) :=
        AdditiveMonoid(T)
      ^ MultiplicativeMonoid(T)
      ^ 0 != 1
      ^ (forall a in T) a * 0 = 0
      ^ (forall a, b, c in T)
            a * (b + c) = a * b + a * c
          ^ (a + b) * c = a * c + b * c

The axiom about multiplication by zero is called the **annihilation property**
The axiom connecting + and * is called the **distributive property**, or **distributivity**

    CommutativeSemiring(T) :=
        Semiring(T)
      ^ commutative(*)

    Ring(T) :=
        AdditiveGroup(T)
      ^ Semiring(T)

    CommutativeRing(T) :=
        AdditiveGroup(T)
      ^ CommutativeSemiring(T)

A **relational concept** is a concept defined on two types
**semimodule** is a relational concept that connects an additive monoid and a commutative semiring:

    Semimodule(T, S) :=
        AdditiveMonoid(T)
      ^ CommutativeSemiring(S)
      ^ *: S x T -> T
      ^ (forall A, B in S) (forall a, b, in T)
            A * (B * a) = (A * B) * a
            (A + B) * a = A * a + B * a
            A * (a + b) = A * a + A * b
                  1 * a = a

If Semimodule(T, S), we say that T is a semimodule over S; we call elements of T **vectors** and elements of S **scalars**

**Theorem 5.1** AdditiveMonoid(T) implies Semimodule(T, N), where scalar multiplication is defined as n * x = x + ... + x (n times).
**Proof.** Let A, B be natural numbers, and let a, b be vectors in T.  Then

    A * (B * a) = (B * a) + ... + (B * a)
                = (a + ... + a) + ... + (a + ... + a)

where there are A parenthesized terms and B copies of a inside each parenthesized term, for a total of A * B copies of a; thus A * (B * a) = (A * B) * a.  Next,

    A * a + B * a = (a + ... + a) + (a + ... + a)

where there are A copies of a in the left parenthesized term and B copies of a in the right parenthesized term, for a total of A + B copies of a; thus A * a + B * a = (A + B) * a.  Furthermore,

    A * (a + b) = (a + b) + ... + (a + b)

and by commutativity of addition, the expression on the left becomes (a + ... + a) + (b + ... + b); thus A * (a + b) = A * a + A * b.  Finally, 1 * a = a follows immediately from the definition of *.

Replacing the additive monoid with an additive group and replacing the semiring with a ring in the definition of a semimodule transforms the semimodule into a **module**:

    Module(S, T) :=
        Semimodule(T, S)
      ^ AdditiveGroup(T)
      ^ Ring(S)

A model is called **partial** when the operations satisfy the axioms where they are defined, but are not everywhere defined

    OrderedAdditiveSemigroup(T) :=
        AdditiveSemigroup(T)
      ^ TotallyOrdered(T)
      ^ (forall a, b, c in T) a < b implies a + c < b + c

    OrderedAdditiveMonoid(T) :=
        OrderedAdditiveSemigroup(T)
      ^ AdditiveMonoid(T)

    OrderedAdditiveGroup(T) :=
        OrderedAdditiveMonoid(T)
      ^ AdditiveGroup(T)

    CancellableMonoid(T) :=
        OrderedAdditiveMonoid(T)
      ^ -: T x T -> T
      ^ (forall a, b in T) b <= a implies
            a - b is defined ^ (a - b) + b = a

    ArchimedeanMonoid(T) :=
        CancellableMonoid(T)
      ^ (forall a, b in T) (a >= 0 ^ b > 0) implies slow_remainder(a, b) terminates
      ^ QuotientType: ArchimedeanMonoid -> Integer

    HalvableMonoid(T) :=
        ArchimedeanMonoid(T)
      ^ half: T -> T
      ^ (forall a, b in T) b > 0 ^ a = b + b implies half(a) = b
