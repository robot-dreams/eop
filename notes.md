## Loose Ends

Project 1.1

## Questions

What would it look like for a programming language to distinguish value types from object types?
How can we tell when a given finite set of procedures actually forms a computational basis for a type?
What does it mean to have a concept defined on more than one type?  What's an example of such a concept?

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
