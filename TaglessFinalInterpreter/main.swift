//
//  main.swift
//  TaglessFinalInterpreter
//
//  Created by Andy Chou on 3/29/17.
//  Copyright © 2017 Andy Chou. All rights reserved.
//

import Foundation
import Bow

//: Playground - noun: a place where people can play

import Cocoa

//  Examples from this paper: http://okmij.org/ftp/tagless-final/course/lecture.pdf
/*
 prettry print, eval, parser
 converting to and from representations.
 
 you have AST but sometimes it makes no sense to do an if statement with a number. syntactically, is ok, but needs to match semantic representation - impossible to encode malformed + ill-typed.
 */
 

//
// Section 2.1: "initial" embedding based on algebraic data types (this is regular "embedding" (aka representation - how to represent it / express the representation of this)). [VS FINAL]
//
indirect enum Exp { //makes it a recursive enum, like activating Haskell mode
    case Lit(Int)
    case Neg(Exp)
    case Add(Exp, Exp)
    //To add Mul: we would need to add this and for all the eval() functions etc. and it's bad here: [this is why we need TAGLESS FINAL [*** instead!]]
    //case Mul(Exp, Exp)
}

let ti1: Exp = .Add(.Lit(8), .Neg(.Add (.Lit(1), .Lit(2)))) //8 + -(1 + 2)

func eval(_ e: Exp) -> Int {
    switch e {
    case let .Lit(n): return n //to return a literal, unwrap the n
    case let .Neg(e): return -eval(e) //negate the evaluation of e
    case let .Add(e1, e2): return eval(e1) + eval(e2)
    }
}

let result1 = eval(ti1)

// pretty printing using initial embedding -- embedding it as an AST
func view(_ e: Exp) -> String { //Converts an expr to string, like pretty-printing it
    switch e {
    case let .Lit(n): return "\(n)"
    case let .Neg(e): return "(- \(view(e)))"
    case let .Add(e1, e2): return "(\(view(e1)) + \(view(e2)))"
    }
}

let str1 = view(ti1)

//This is a final embedding: what if we consider Lit not as ((Int) -> TaglessFinalInterpreter.Exp) but as Int to any representation (repr) and not just Exp. It's a generic return type.
//This means ExpressionSemantics
protocol ExpSym { //this is like a typeclass (concept)
    associatedtype repr //this is like a template parameter
    func lit(_ n: Int) -> repr
    func neg(_ e: repr) -> repr //repr can be an int OR STRING OR ANYTHING. it's generic.
    func add(_ e1: repr, _ e2: repr) -> repr
}

//In the domain of ints, it makes sense that add actually adds them, and so on.
class IntExpSym: ExpSym {
    typealias repr = Int //we now say what the repr is, as an Int
    func lit(_ n: Int) -> repr { return n }
    func neg(_ e: repr) -> repr { return -e }
    func add(_ e1: repr, _ e2: repr) -> repr { return e1 + e2 } //No recursion, we already "evaluated" it as an int! (whereas previously our eval function terminates at a potentially unknown point.). And even no tagged unions, so its up to compiler optimizations to decide what to do.
}

//To make a pretty printer:
class StringExpSym: ExpSym {
    typealias repr = String
    func lit(_ n: Int) -> repr { return "\(n)" }
    func neg(_ e: repr) -> repr { return "(- \(e))" }
    func add(_ e1: repr, _ e2: repr) -> repr { return "(\(e1) + \(e2))" }
}

func tf1<E: ExpSym>(_ v: E) -> E.repr {
    return v.add(v.lit(8), v.neg(v.add(v.lit(1), v.lit(2))))
} //the type depends on how we interpret it! -- literally abstract syntax.

let tf2: Int = tf1(IntExpSym())
let ts2: String = tf1(StringExpSym())

//
// Section 2.2: expression problem
//

//goal: add Mul. problem with OOP: we have changing requirements. if we add multiplication then things break like our old eval functions wont work because it, if it were switch statement, breaks because doesn't consider that case. Need to change old code, which is bad.


// Using Swift's protocol extensions doesn't work naturally; we don't have a specific implementation of mul here.

//we don't know what repr is so we cant do anything:

//extension ExpSym {
//    func mul(_ e1: repr, _ e2: repr) -> repr {
//        ...
//    }
//}

// Instead we create a new protocol to add mul
protocol MulSym { //[***]
//side note: in haskell we dont have to have mulsym inherit from expsym.
    associatedtype repr
    func mul(_ e1: repr, _ e2: repr) -> repr
}

class IntMulSym: IntExpSym, MulSym { //[***] didn't need to recompile old code! and no dynamic dispatch either.
    func mul(_ e1: Int, _ e2: Int) -> Int {
        return e1 * e2
    }
}

class StringMulSym: StringExpSym, MulSym {
    func mul(_ e1: String, _ e2: String) -> String {
        return "(\(e1) * \(e2))"
    }
}

//Tagless Final Multiplication (Example) 1.
//We have the same data type but its value depends on how we view it!
func tfm1<E: MulSym & ExpSym>(_ v: E) -> E.repr {
    return v.add(v.lit(8), v.neg(v.mul(v.lit(1), v.lit(2))))
}
/*
 (lldb) expr tfms1
 (String) $R4 = "(8 + (- (1 * 2)))"
 (lldb) expr tfm1
 error: <EXPR>:3:1: error: generic parameter 'E' could not be inferred
 tfm1
 ^
 
 (lldb) type tfm1
 invalid command 'type tfm1'.
 (lldb) expr type(of: tfm1)
 error: <EXPR>:3:1: error: expression type '(_) -> _' is ambiguous without more context
 type(of: tfm1)
 ^~~~
 
 (lldb) expr type(of: tfmi1)
 (Int.Type) $R6 = Int
 (lldb)
 */

func tfm2<E: MulSym & ExpSym>(_ v: E) -> E.repr {
    return v.mul(v.lit(7), tf1(v))
}

let tfmi1 = tfm1(IntMulSym())
let tfms1 = tfm1(StringMulSym()) //note: code re-use successful! "this scales instantly, i think."

//
// Section 2.3: de-serialization
//

//This is one way to represent an AST.
// Oddly, for a paper that is about the final embedding, the author chose to describe Tree as an initial embedding.
indirect enum Tree {
    case Leaf(String)
    case Node(String, [Tree])
}

//MARK: Exercise: tagless final tree

//This is one way to represent an AST.
protocol TreeF {
    associatedtype repr
    func leaf(_ e: String) -> repr
    func node(_ s: String, _ l: [repr]) -> repr
    //                              ^-- repr says even the trees in the list are generic. we dont say what the type is, just repr.
}

//MARK: continued

extension Tree: CustomStringConvertible { //This is a "Show" typeclass from Haskell
    var description: String {
        switch self {
        case let .Leaf(str): return "Leaf '\(str)'"
        case let .Node(str, subtrees):
            let showSubtrees = subtrees.map { $0.description }.joined(separator: ", ")
            return "Node '\(str)' [\(showSubtrees)]"
        }
    }
}

//MARK: Exercise: tagless final tree

//This is how to evaluate a tree in the domain of strings.
//(We could even represent trees as JSON...)
class StringTreeF: TreeF {
    //We're saying that our tagless final tree can be interpreted as a string.
    typealias repr = String
    func leaf(_ e: String) -> repr {
        return "Leaf '\(e)'"
    }
    
    func node(_ s: String, _ l: [repr]) -> repr {
        let subtrees = l.joined(separator: ", ")
        return "Node '\(s)' [\(subtrees)]"
    }
}

//Exercise: interpret as something else
//Interpret generic trees in the domain of concrete trees.
//Purpose: to show that our representation can be made concrete again.
class TreeTreeF: TreeF {
    //We're saying that our tagless final tree can be interpreted as a string.
    typealias repr = Tree
    
    func leaf(_ e: String) -> repr {
        return .Leaf(e)
    }
    
    func node(_ s: String, _ l: [repr]) -> repr {
        return .Node(s, l)
    }
}

//Exercise: make a reverse string
class ReverseStringTreeF: TreeF {
    //We're saying that our tagless final tree can be interpreted as a string.
    typealias repr = String
    func leaf(_ e: String) -> repr {
        return "Leaf '\(String(e.reversed()))'"
    }
    
    func node(_ s: String, _ l: [repr]) -> repr {
        let subtrees = l.joined(separator: ", ")
        return "Node '\(String(s.reversed()))' [\(subtrees)]"
    }
}

//MARK: continued

class TreeSym: ExpSym {
    typealias repr = Tree
    
    func lit(_ n: Int) -> Tree {
        return .Node("Lit", [.Leaf(String(n))])
    }
    
    func neg(_ e: Tree) -> Tree {
        return .Node("Neg", [e])
    }
    
    func add(_ e1: Tree, _ e2: Tree) -> Tree {
        return .Node("Add", [e1, e2])
    }
}

//MARK: Exercise: tagless final tree

struct TreeSymF<E: TreeF>: ExpSym {
    typealias repr = E.repr
    let v: E //limitation of swift..?

    func lit(_ n: Int) -> E.repr {
        return v.node("Lit", [v.leaf(String(n))])
    }
    
    func neg(_ e: E.repr) -> E.repr {
        return v.node("Neg", [e])
    }
    
    func add(_ e1: E.repr, _ e2: E.repr) -> E.repr {
        return v.node("Add", [e1, e2])
    }
}

//MARK: continued

let tf1_tree = tf1(TreeSym()) //`func tf1<E: ExpSym>(_ v: E)` takes some generic structure and we interpret it in the domain[<the semantic domain. denotational semantics: denotation(translation from sign to meaning) of an expression depends on the domain you are talking about it in: in a string, 5 has the meaning of part of the string; in an integer literal it is an integer.] of trees now.   //NOTE: application example: VECS entity component system Position.x changes meaning in a method call; otherwise it means a type.
//MARK: Exercise: tagless final tree
let tf1_treeF = tf1(TreeSymF(v: StringTreeF()))
let tf1_treeTreeF = tf1(TreeSymF(v: TreeTreeF()))
let tf1_reversedStringTreeF = tf1(TreeSymF(v: ReverseStringTreeF()))
tf1_treeTreeF.description
tf1_reversedStringTreeF.description
//MARK: continued
tf1_tree.description //serialization!
//MARK: Exercise: tagless final tree
tf1_treeF.description
//MARK: continued

//Deserialization:
func fromTree<E: ExpSym>(_ tree: Tree) -> (_ e: E) -> E.repr? { //"?": Yay, Nothing or Just
    return { e in
        switch tree {
        case let .Node("Lit", subtree) where subtree.count == 1:
            if case let .Leaf(str) = subtree[0], let n = Int(str) {
                return e.lit(n) //generic representation! so good. (because returns E.rep -- we are converting from a tree to the generic representation.)
            }
            return nil
        case let .Node("Neg", subtree) where subtree.count == 1: //In Haskell, it's easier with liftM, liftM2, etc. -- lifting a pure computation into the monad.
            if let subexpr = fromTree(subtree[0])(e) {
                return e.neg(subexpr)
            }
            return nil
        case let .Node("Add", subtree) where subtree.count == 2:
            if let a = fromTree(subtree[0])(e), let b = fromTree(subtree[1])(e) {
                return e.add(a, b)
            }
            return nil
        default:
            return nil
        }
    }
}

// The following line shows that a polymorphic function can't be returned from a function. The returned function must have a concrete type inferred.
// let tree_fn = fromTree(tf1_tree)

//fromTree(tf1_tree) : converts a serialized tree into a generic representation.
let tf1_string = fromTree(tf1_tree)(StringExpSym()) //interpret it as a string

let tf1_eval = fromTree(tf1_tree)(IntExpSym())

//Example from the paper, nvm:
class DuplicateSym<E1, E2>: ExpSym where E1: ExpSym, E2: ExpSym {
    typealias R1 = E1.repr
    typealias R2 = E2.repr
    typealias repr = (R1, R2)
    let e1: E1
    let e2: E2
    
    init(_ e1: E1, _ e2: E2) {
        self.e1 = e1
        self.e2 = e2
    }
    
    func lit(_ n: Int) -> (R1, R2) {
        return (e1.lit(n), e2.lit(n))
    }
    
    func neg(_ e: (R1, R2)) -> (R1, R2) {
        return (e1.neg(e.0), e2.neg(e.1))
    }
    
    func add(_ e1: (R1, R2), _ e2: (R1, R2)) -> (R1, R2) {
        return (self.e1.add(e1.0, e2.0), self.e2.add(e1.1, e2.1))
    }
}

func >>=<E1: ExpSym, E2: ExpSym>(e1: E1, e2: E2) -> DuplicateSym<E1,E2> {
    return DuplicateSym(e1, e2)
}

let multiSym = IntExpSym() >>= StringExpSym() >>= TreeSym()
if let (val, (str, tree)) = fromTree(tf1_tree)(multiSym) {
    print("val: \(val)")
    print("str: \(str)")
    print("tree: \(tree)")
}


// Adding mult to deserialization

class TreeMulSym: TreeSym, MulSym {
    func mul(_ e1: Tree, _ e2: Tree) -> Tree {
        return .Node("Mul", [e1, e2])
    }
}

//how to deserialize a multiplication node. reuses how to deserialize a tree with "fromTree" recursive calls.
func fromMulTree<E: MulSym & ExpSym>(_ tree: Tree) -> (_ e: E) -> E.repr? {
    return { e in
        if case let .Node("Mul", subtree) = tree, subtree.count == 2 {
            if let a = fromTree(subtree[0])(e), let b = fromTree(subtree[1])(e) {
                return e.mul(a, b)
            }
        }
        return fromTree(tree)(e)
    }
}

//class DuplicateMulSym<E1, E2>: DuplicateSym<E1,E2>, MulSym where E1: MulSym, E2: MulSym {
//    func mul(_ e1: (R1, R2), _ e2: (R1, R2)) -> (R1, R2) {
//        return (self.e1.mul(e1.0, e2.0), self.e2.mul(e1.1, e2.1))
//    }
//}
//
//func tm1<E: MulSym>(_ e: E) -> E.repr {
//    return e.mul(e.add(e.lit(42), e.neg(e.lit(10))), e.lit(7))
//}
//
//let tmtree = tm1(TreeMulSym()) //This is a way better way of basically extending with inheritance
//let multiMulSym = DuplicateMulSym(IntMulSym(), DuplicateMulSym(StringMulSym(), TreeMulSym()))
//if let (val, (str, tree)) = fromMulTree(tmtree)(multiMulSym) {
//    print("val: \(val)")
//    print("str: \(str)")
//    print("tree: \(tree)")
//}

//
// Section 2.4: Pattern Matching
//

//goal: compiler optimizations: turn ----5 into 5. so much easier to express with pattern matching than with imperative languages. This is like a parse tree / AST. Do a pass over the code where we optimize.

// Using the Initial style
func pushNeg(_ e: Exp) -> Exp { //****not a fold because i give a structure and it returns a structure
    switch e {
    case .Lit(_): return e //no negation at all, no optimization.
    case .Neg(.Lit(_)): return e //we only optimize it when you have double negation, but here theres only one.
    case let .Neg(.Neg(e)): return pushNeg(e)
    case let .Neg(.Add(e1, e2)): return .Add(pushNeg(.Neg(e1)), pushNeg(.Neg(e2))) //distribute the negation over the adds. use a math law! we can prove it with math. It pushes the negation down... its like bubble pushing from digital systems.
    case let .Add(e1, e2): return .Add(pushNeg(e1), pushNeg(e2))
    }
}

//****fold: means to collapse a structure; unfold is make like a number into a list with range(5) <-- is an unfold.
//eval is a fold.
//pretty printing is also a fold because it makes a string which is a single value.

let ti1_norm = pushNeg(ti1)
view(ti1_norm) //ti1, but "optimized"... not really though here, only two negations is actually useful because they would cancel.
//disjunction normal forms: we can convert a bool expr to a combination of and's and or's.
eval(ti1_norm)

// Using the Final style (super-generic way, instead of the AST way above)

//we cant pattern match on functions like from the protocol ExpSym, so we need context-sensitive transform. instead of context-free. context-free: doesn't matter how we got here.
enum Ctx { case Pos, Neg } //this is whether we start with pos or neg. the initial context!

// The final style of pattern matching doesn't really translate well to Swift because functions cannot be built up from argument pattern matching
class ExpPushNegSym<E: ExpSym>: ExpSym { //Do a transformation on a generic ExpSym and produce another ExpSym, so it works extensibly too. we can work abstractly without concrete things
    typealias repr = (Ctx) -> E.repr //repr in this implementation of the protocol allows us to supply a context, get generic representation that applies the context. for example, if the context is Neg, we negate E.repr and return it.
    //substitute E as a string for example.
    let e: E
    
    init(_ e: E) {
        self.e = e
    }
    
    //need to implement these since we are implementing a protocol.
    //func lit(_ n: Int) -> repr       =            func lit(_ n: Int) -> ((Ctx) -> E.repr)         [using equational reasoning]
    func lit(_ n: Int) -> repr {
        return { $0 == .Pos ? self.e.lit(n) : self.e.neg(self.e.lit(n)) } //returning a lambda that takes in the context as $0 and checks if it's positive. only negate if it's neg. and neg will be `func neg(_ e: repr) -> repr { return "(- \(e))" }` if we are pretty printing, or it'll be negation of an int  for IntExpSym!
    }
    
    //func neg(_ e: @escaping repr) -> repr        =        func neg(_ e: @escaping ((Ctx) -> E.repr)) -> ((Ctx) -> E.repr)       ---> takes a function from context to e repr and returns that type too.
    func neg(_ e: @escaping repr) -> repr { //@escaping basically puts it into a capture list so we can call the lambda later.
        return { $0 == .Pos ? e(.Neg) : e(.Pos) } //the function take a context, so we have to accept the context ($0). Then we must return a type E.repr, but we only have e, a function from (Ctx) -> E.repr. Pass the context to e. If we pass context to e, we get an E.repr. *****We pass a context based on our given context. --- it's like a global flag and we are changing it.*****
    }
    
    //func add(_ e1: @escaping repr, _ e2: @escaping repr) -> repr
    //  =      func add(_ e1: @escaping ((Ctx) -> E.repr), _ e2: @escaping ((Ctx) -> E.repr)) -> ((Ctx) -> E.repr)           [using typealias repr = (Ctx) -> E.repr]
    func add(_ e1: @escaping repr, _ e2: @escaping repr) -> repr {
        return { self.e.add(e1($0), e2($0)) } //quote-unquote the recursive calls like "case let .Add(e1, e2): return .Add(pushNeg(e1), pushNeg(e2))"
    }
}

let pushed = tf1(ExpPushNegSym(StringExpSym()))(.Pos)

/*
 (lldb) expr tf1(StringExpSym())
(TaglessFinalInterpreter.StringExpSym.repr) $R4 = "(8 + (- (1 + 2)))"
(lldb) expr tf1(ExpPushNegSym(StringExpSym()))
((TaglessFinalInterpreter.Ctx) -> TaglessFinalInterpreter.StringExpSym.repr) $R6 = 0x00000001011fb9a0
(lldb) expr tf1(ExpPushNegSym(StringExpSym()))(.Pos)
(TaglessFinalInterpreter.StringExpSym.repr) $R8 = "(8 + ((- 1) + (- 2)))"
(lldb) expr tf1(ExpPushNegSym(TreeExpSym()))(.Pos)

error: <EXPR>:3:19: error: use of unresolved identifier 'TreeExpSym'
tf1(ExpPushNegSym(TreeExpSym()))(.Pos)
                  ^~~~~~~~~~

error: <EXPR>:3:19: error: use of unresolved identifier 'TreeExpSym'
tf1(ExpPushNegSym(TreeExpSym()))(.Pos)
                  ^~~~~~~~~~

error: <EXPR>:3:19: error: use of unresolved identifier 'TreeExpSym'
tf1(ExpPushNegSym(TreeExpSym()))(.Pos)
                  ^~~~~~~~~~

(lldb) expr tf1(ExpPushNegSym(TreeSym()))(.Pos)
(TaglessFinalInterpreter.TreeSym.repr) $R10 = Node {
  Node = {
    0 = "Add"
    1 = 2 values {
      [0] = Node {
        Node = {
          0 = "Lit"
          1 = 1 value {
            [0] = Leaf {
              Leaf = "8"
            }
          }
        }
      }
      [1] = Node {
        Node = {
          0 = "Add"
          1 = 2 values {
            [0] = Node {
              Node = {
                0 = "Neg"
                1 = 1 value {
                  [0] = Node {
                    Node = {
                      0 = "Lit"
                      1 = 1 value {
                        [0] = Leaf {
                          Leaf = "1"
                        }
                      }
                    }
                  }
                }
              }
            }
            [1] = Node {
              Node = {
                0 = "Neg"
                1 = 1 value {
                  [0] = Node {
                    Node = {
                      0 = "Lit"
                      1 = 1 value {
                        [0] = Leaf {
                          Leaf = "2"
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}
(lldb) expr tf1(ExpPushNegSym(TreeSym()))(.Pos).description
(String) $R12 = "Node \'Add\' [Node \'Lit\' [Leaf \'8\'], Node \'Add\' [Node \'Neg\' [Node \'Lit\' [Leaf \'1\']], Node \'Neg\' [Node \'Lit\' [Leaf \'2\']]]]"
(lldb) expr tf1(TreeSym()).description
(String) $R14 = "Node \'Add\' [Node \'Lit\' [Leaf \'8\'], Node \'Neg\' [Node \'Add\' [Node \'Lit\' [Leaf \'1\'], Node \'Lit\' [Leaf \'2\']]]]"
(lldb)
 */

//tagless final means we can use the type checker that we already have; whereas what's bad is that in the indirect enum Exp, We could have Apply but then do Lit 3 applied to 5 which is bad in our type system. We have it so actually you cant do this because the [IMPLEMENT LATER its in the paper.]
//TODO: later, implement in C++ if you can..
//this is just like writing a syntax checker for SQL.!

//TODO: implement rest of paper with Ben
let a = 1; //(no-op)



//This was a fun excursion, but there's only one type: int. tagless final shines with more types. eval never crashes because only lit, neg, and add, so every possible combination of this is valid... but if we get more types like booleans then not every representation is valid.


/*
 template<typename Vector> void doSomething(Vector v) {
    v.push_back(1);
 }
 */

//We need higher kinded types.
protocol Semantics {
    associatedtype repr
    
    func int(_ i: Int) -> Kind<repr, Int>
    func add(_ i1: Kind<repr, Int>, _ i2: Kind<repr, Int>) -> Kind<repr, Int>
    
    func lam<a, b>(_ i1: Kind<repr, a>, _ i2: Kind<repr, b>) -> Kind<repr, (a) -> b> // lam :: (repr a→repr b)→repr (a→b)
    func app<a, b>(_ f1: Kind<repr, (a) -> b>, _ i2: Kind<repr, a>) -> Kind<repr, b> // app :: repr (a→b)→repr a→repr b
}

func sum(_ array: [Int]) -> Int {
    guard array.first != nil else { return 0 }
    return array.reduce(0) { acc, a in acc + a}
} //equivalent to `sum = foldr (+) 0` in Haskell

let sumTest = sum(Array(1...5))

/*
 
 /// Combines the elements of this array using their `MonoidK` instance.
    ///
    /// - Parameter fga: Structure to be reduced.
    /// - Returns: A value in the context providing the `MonoidK` instance.
    func reduceK<G: MonoidK, A>() -> Kind<G, A> where Element == Kind<G, A> {
        self.k().reduceK()
    }
 
 
 `reduce(_:)`:
 A semigroup is basically that you can do associativity using parenethesis.
 */

var b = 2

//ad-hoc poloymorphism is typeclasses/protocols

//Either is a type-level function : type to type to type. takes two types and returns a type.
//https://bow-swift.io/docs/fp-concepts/higher-kinded-types/ : F to abstract away the Either or Validated type. :
/* this does NOT work in swift:
 func divide<F: ErrorSuccessRepresentable>(x: Int, y: Int) -> F<DivideError, Int> {
 guard y != 0 else { return .failure(.divisionByZero)
 return .success(x / y)
 }
 */
//WE CAN generalize the container such as std::vector so it doesnt just accept a type and waiting for type.

//types have a type, and the type of a type is called its kind. Int has kind * which is a concrete type. Int, Bool, String, Vehicle, etc.
//*->* is Array<Element>

//TODO: what are higher rank types?
