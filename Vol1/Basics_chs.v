(** * 基础: Coq中的函数式编程 *)

(* 提示:

          #####################################################
          ###               请勿公开发布解答                 ###
          #####################################################

   (原因参见[序言]。)
*)

(* ################################################################# *)
(** * 引言 *)

(** 函数式编程是建立在一个简单的日常数学直感之上的: 如果一个过程或方法
    没有任何副作用，那么（不考虑效率）我们只需要了解它是如何把输入映射到
    结果的————也就是说，我们可以就把它当作一个具体的计算数学函数的方法。
    这是“函数式编程”中“函数式”一词的一层原因。程序和简单数学对象之间的
    直接联系使得关于程序行为的形式的正确性证明和完备的非形式推导成为可能。

    函数式编程之所以是“函数式”的另一层原因在于它强调了把函数（或方法）作为
    _第一类_值————亦即那些可以被当作实参传递给其他函数，作为返回值，作为
    数据结构的一部分等等的值。把函数当作数据使得大量实用且强大的编程惯用法
    得以诞生。

    函数式语言的其他常见特征包括_代数数据类型_和_模式匹配_，它们让创建和
    操作丰富的数据结构变得更简单。还有支持抽象化和代码重用的复杂的_多态类
    型系统_。Coq提供所有这些特性。
    
    本章的前半介绍Coq的函数式编程语言最基础的组件，_Gallina_。后半介绍一
    些基本的_策略_，它们可以用来证明Coq程序的性质。*)

(* ################################################################# *)
(** * 数据与函数 *)
(* ================================================================= *)
(** ** 枚举类型 *)

(** Coq一个值得一提的特征就是，它的自带特性_极其_少。举例来说，它并没有提
    供原子数据类型（布尔，整数，字符串等），而是提供了一个强大的机制来从头
    定义新数据类型。我们熟悉的这些类型就是例子。

    Coq的发行版自然预载了包含布尔值，数值以及很多常见数据类型定义（如列表
    和哈希表）的标准库。但这些库中的定义并没有任何神奇或是原始之处。为了证明
    这一点，我们将回顾在这一课中需要的所有定义，而不是直接从标准库中直接
    取用。 *)

(* ================================================================= *)
(** ** 一周之中的日子 *)

(** 为了理解这个定义机制是如何运作的，我们从一个简单的例子开始。下面的定义
    告诉Coq我们正在定义一套新的数据值————_类型_。 *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** 这个类型叫作[day]， 它的成员有[monday]，[tuesday]等等。第二行开始可以念
    成“[monday]是一个[day]，[tuesday]是一个[day]...”。
    
    定义[day]之后，我们可以来写使用这些日子的函数了。*)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** 需要注意的一点是，这里的参数和返回类型都是显式定义的。就像大多数函数式语言
    一样，如果没有显式定义的话，Coq通常可以自己推断出这些类型————也就是说它可
    以进行_类型推断_————但为了可读性我们通常会加上它们。*)

(** 定义了函数之后，我们应该检查它能否通过一些测试。在Coq中你有三种方法来测试。
    第一种是用[Compute]命令来求一个使用了[next_weekday]函数的复合表达式的值。*)

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

(** (我们会在注释中写出Coq的输出结果。但如果你手边就有电脑的话，不妨在你最喜欢
    的IDE里启动Coq的解释器————CoqIde或者Proof General————来自己尝试这些例子。
    载入这个文件，[Basics_chs.v]，找到上面的例子，提交给Coq，然后观察结果。)

    第二种是用Coq example的形式记录下我们_想要的_结果： *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** 这个声明做了两件事：首先它做了一个断言（[saturday]之后的第二个工作日是
    [tuesday]），然后它给了这个断言一个名字，这样你以后就可以再使用它了。做
    了这个断言之后，我们就可以像这样让Coq来验证：*)

Proof. simpl. reflexivity.  Qed.

(** 细节暂时并不重要（我们之后会提到一点的），但这基本上可以念成“我们刚做的
    断言可以这样证明：在一些简化之后，观察到等式两边的值相同。”

    第三种是让Coq从我们的[定义]中_提取_出一个使用一些更传统的，并且具有更好
    的编译器的编程语言（OCaml，Scheme或是Haskell）的程序。这一功能十分有趣，
    因为它能把我们在Gallina中写的证明过正确性的算法转换成高效的机器码。（当然，
    我们相信OCaml/Scheme/Haskell编译器，以及Coq提取功能的正确性，但这仍然是
    与大多数软件的开发方式有很大不同的。）事实上，这是开发Coq的主要用途之一。
    在后面的章节我们会回到这个话题。*)

(* ================================================================= *)
(** ** 提交作业的指南 *)

(** 如果你在课程中使用本书，你的老师可能会用一个脚本来给你的作业打分。为了使
    这些脚本能正确打分（这样你才能有成绩！），请小心遵守如下的准则：
      - 评分脚本可能是通过提取标记过的区域来打分的。所以请你不要修改限定习题的
        “标记”：比如习题的标题，名字，结尾的“空白方块”等。不要修改这些标记。
      - 不要删除习题。如果你不想做某个题（比如它是选做的，或者你不会做），你可
        以让你的证明处于未完成的状态。但这时请确保它最后有[Admitted]（而不是
        [Abort]之类的）。 *)

(* ================================================================= *)
(** ** 布尔 *)

(** 类似地，我们可以定义布尔类型[bool]。它有两个成员，[true]和[false]。*)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(** 尽管我们为了从头建立一切而定义了布尔，Coq是有自己的布尔实现和一整套有用的
    函数和引理的。（感兴趣的话可以看看Coq库文档里的[Coq.Init.Datatypes]。）
    我们会尽可能让我们自己的定义以及定理和标准库里的重名。 
    
    布尔函数可以用同样的方式定义：*)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** 最后两个定义展示了Coq定义多参数函数的语法。调用多参数函数的语法可以参见下面的
    “单元测试”。它们为[orb]函数提供了一个完整的规格————真值表。*)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** 我们还可以为刚定义的这些布尔函数引入一些熟悉的语法。[Infix]命令可以为一个既存
的定义指定一个新的符号表示。 *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** _关于符号的说明_: 在[.v]文件中, 我们用方括号来分隔注释中的Coq代码。文档工具
    [coqdoc]也使用这一规则，这样就把它们和周围的文字区分开了。在HTML版中，这些文
    字会用[不同字体]显示。

    [Admitted]命令可以在不完整的证明中作为占位符。我们会在习题中使用它，借此来告
    诉你我们把它留给你了————你需要把[Admitted]改成实际的证明。*)

(** **** 练习: 1星 (nandb)  *)
(** 删掉“[Admitted.]”并完成该函数的定义；然后确保[Example]断言可以被Coq验证。（删
    掉“[Admitted.]”，照着上面[orb]的例子完成每个证明。）该函数在至少一个输入为
    [false]时返回[true]。*)

Definition nandb (b1:bool) (b2:bool) : bool
  (* 把这行换成 “:= _你的定义_ .” *). Admitted.

Example test_nandb1:               (nandb true false) = true.
(* 填空 *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* 填空 *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* 填空 *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* 填空 *) Admitted.
(** [] *)

(** **** 练习: 1星 (andb3)  *)
(** 类似地，给[andb3]函数完成定义和断言。 该函数在全部输入均为[true]时返回[true]，
    否则返回[false]。 *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  (* 把这行换成 “:= _你的定义_ .” *). Admitted.

Example test_andb31:                 (andb3 true true true) = true.
(* 填空 *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* 填空 *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* 填空 *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* 填空 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 函数类型 *)

(** Every expression in Coq has a type, describing what sort of
    thing it computes. The [Check] command asks Coq to print the type
    of an expression. *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)

Check negb.
(* ===> negb : bool -> bool *)

(** The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool -> bool -> bool], can
    be read, "Given two inputs, both of type [bool], this function
    produces an output of type [bool]." *)

(* ================================================================= *)
(** ** Compound Types *)

(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements, each of which is just a bare constructor.  Here is a
    more interesting type definition, where one of the constructors
    takes an argument: *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

(** Let's look at this in a little more detail.

    Every inductively defined type ([day], [bool], [rgb], [color],
    etc.) contains a set of _constructor expressions_ built from
    _constructors_ like [red], [primary], [true], [false], [monday],
    etc.  The definitions of [rgb] and [color] say how expressions in
    the sets [rgb] and [color] can be built:

    - [reg], [green], and [blue] are the constructors of [rgb];
    - [black], [white], and [primary] are the constructors of [color];
    - the expression [red] belongs to the set [rgb], as do the
      expressions [green] and [blue];
    - the expressions [black] and [white] belong to the set [color];
    - if [p] is an expression belonging to the set [rgb], then
      [primary p] (pronounced "the constructor [primary] applied to
      the argument [p]") is an expression belonging to the set
      [color]; and
    - expressions formed in these ways are the _only_ ones belonging
      to the sets [rgb] and [color]. *)

(** We can define functions on colors using pattern matching just as
    we have done for [day] and [bool]. *)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

(** Since the [primary] constructor takes an argument, a pattern
    matching [primary] should include either a variable (as above) or
    a constant of appropriate type (as below). *)

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(** The pattern [primary _] here is shorthand for "[primary] applied
    to any [rgb] constructor except [red]."  (The wildcard pattern [_]
    has the same effect as the dummy pattern variable [p] in the
    definition of [monochrome].) *)

(* ================================================================= *)
(** ** Modules *)

(** Coq provides a _module system_, to aid in organizing large
    developments.  In this course we won't need most of its features,
    but one is useful: If we enclose a collection of declarations
    between [Module X] and [End X] markers, then, in the remainder of
    the file after the [End], these definitions are referred to by
    names like [X.foo] instead of just [foo].  We will use this
    feature to introduce the definition of the type [nat] in an inner
    module so that it does not interfere with the one from the
    standard library (which we want to use in the rest because it
    comes with a tiny bit of convenient special notation).  *)

Module NatPlayground.

(* ================================================================= *)
(** ** Numbers *)

(** An even more interesting way of defining a type is to allow its
    constrctors to take arguments from the very same type -- that is,
    to allow the rules describing its elements to be _inductive_.

    For example, we can define (a unary representation of) natural
    numbers as follows: *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** The clauses of this definition can be read:
      - [O] is a natural number (note that this is the letter "[O],"
        not the numeral "[0]").
      - [S] can be put in front of a natural number to yield another
        one -- if [n] is a natural number, then [S n] is too. *)

(** Again, let's look at this in a little more detail.  The definition
    of [nat] says how expressions in the set [nat] can be built:

    - [O] and [S] are constructors;
    - the expression [O] belongs to the set [nat];
    - if [n] is an expression belonging to the set [nat], then [S n]
      is also an expression belonging to the set [nat]; and
    - expressions formed in these two ways are the only ones belonging
      to the set [nat]. *)

(** The same rules apply for our definitions of [day], [bool],
    [color], etc.

    The above conditions are the precise force of the [Inductive]
    declaration.  They imply that the expression [O], the expression
    [S O], the expression [S (S O)], the expression [S (S (S O))], and
    so on all belong to the set [nat], while other expressions built
    from data constructors, like [true], [andb true false], [S (S
    false)], and [O (O (O S))] do not.

    A critical point here is that what we've done so far is just to
    define a _representation_ of numbers: a way of writing them down.
    The names [O] and [S] are arbitrary, and at this point they have
    no special meaning -- they are just two different marks that we
    can use to write down numbers (together with a rule that says any
    [nat] will be written as some string of [S] marks followed by an
    [O]).  If we like, we can write essentially the same definition
    this way: *)

Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

(** The _interpretation_ of these marks comes from how we use them to
    compute. *)

(** We can do this by writing functions that pattern match on
    representations of natural numbers just as we did above with
    booleans and days -- for example, here is the predecessor
    function: *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)

End NatPlayground.

(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary arabic numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in arabic form by default: *)

Check (S (S (S (S O)))).
  (* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).
  (* ===> 2 : nat *)

(** The constructor [S] has the type [nat -> nat], just like 
    [pred] and functions like [minustwo]: *)

Check S.
Check pred.
Check minustwo.

(** These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference between the
    first one and the other two: functions like [pred] and [minustwo]
    come with _computation rules_ -- e.g., the definition of [pred]
    says that [pred 2] can be simplified to [1] -- while the
    definition of [S] has no such behavior attached.  Although it is
    like a function in the sense that it can be applied to an
    argument, it does not _do_ anything at all!  It is just a way of
    writing down numbers.  (Think about standard arabic numerals: the
    numeral [1] is not a computation; it's a piece of data.  When we
    write [111] to mean the number one hundred and eleven, we are
    using [1], three times, to write down a concrete representation of
    a number.)

    For most function definitions over numbers, just pattern matching
    is not enough: we also need recursion.  For example, to check that
    a number [n] is even, we may need to recursively check whether
    [n-2] is even.  To write such functions, we use the keyword
    [Fixpoint]. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity.  Qed.

(** (You will notice if you step through these proofs that
    [simpl] actually has no effect on the goal -- all of the work is
    done by [reflexivity].  We'll see more about why that is shortly.)

    Naturally, we can also define multi-argument functions by
    recursion.  *)

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Adding three to two now gives us five, as we'd expect. *)

Compute (plus 3 2).

(** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))]
      by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))]
      by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))]
      by the second clause of the [match]
==> [S (S (S (S (S O))))]
      by the first clause of the [match]
*)

(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** You can match two expressions at once by putting a comma
    between them: *)

Fixpoint minus (n m:nat) : nat :=
  match (n, m) with
  | (O   , _)    => O
  | (S _ , O)    => n
  | (S n', S m') => minus n' m'
  end.

(** Again, the _ in the first line is a _wildcard pattern_.  Writing
    [_] in a pattern is the same as writing some variable that doesn't
    get used on the right-hand side.  This avoids the need to invent a
    variable name. *)

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(** **** 练习: .星 (factorial)  *)
(** Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Coq. *)

Fixpoint factorial (n:nat) : nat
  (* 把这行换成 “:= _你的定义_ .” *). Admitted.

Example test_factorial1:          (factorial 3) = 6.
(* 填空 *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* 填空 *) Admitted.
(** [] *)

(** We can make numerical expressions a little easier to read and
    write by introducing _notations_ for addition, multiplication, and
    subtraction. *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

(** (The [level], [associativity], and [nat_scope] annotations
    control how these notations are treated by Coq's parser.  The
    details are not important for our purposes, but interested readers
    can refer to the optional "More on Notation" section at the end of
    this chapter.)

    Note that these do not change the definitions we've already made:
    they are simply instructions to the Coq parser to accept [x + y]
    in place of [plus x y] and, conversely, to the Coq pretty-printer
    to display [plus x y] as [x + y]. *)

(** When we say that Coq comes with almost nothing built-in, we really
    mean it: even equality testing for numbers is a user-defined
    operation!  We now define a function [beq_nat], which tests
    [nat]ural numbers for [eq]uality, yielding a [b]oolean.  Note the
    use of nested [match]es (we could also have used a simultaneous
    match, as we did in [minus].) *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** The [leb] function tests whether its first argument is less than or
  equal to its second argument, yielding a boolean. *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** 练习: .星 (blt_nat)  *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined function. *)

Definition blt_nat (n m : nat) : bool
  (* 把这行换成 “:= _你的定义_ .” *). Admitted.

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* 填空 *) Admitted.
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* 填空 *) Admitted.
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* 填空 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Proof by Simplification *)

(** Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.
    Actually, we've already started doing this: each [Example] in the
    previous sections makes a precise claim about the behavior of some
    function on some particular inputs.  The proofs of these claims
    were always the same: use [simpl] to simplify both sides of the
    equation, then use [reflexivity] to check that both sides contain
    identical values.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved just
    by observing that [0 + n] reduces to [n] no matter what [n] is, a
    fact that can be read directly off the definition of [plus].*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.

(** (You may notice that the above statement looks different in
    the [.v] file in your IDE than it does in the HTML rendition in
    your browser, if you are viewing both. In [.v] files, we write the
    [forall] universal quantifier using the reserved identifier
    "forall."  When the [.v] files are converted to HTML, this gets
    transformed into an upside-down-A symbol.)

    This is a good place to mention that [reflexivity] is a bit
    more powerful than we have admitted. In the examples we have seen,
    the calls to [simpl] were actually not needed, because
    [reflexivity] can perform some simplification automatically when
    checking that two sides are equal; [simpl] was just added so that
    we could see the intermediate state -- after simplification but
    before finishing the proof.  Here is a shorter proof of the
    theorem: *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(** Moreover, it will be useful later to know that [reflexivity]
    does somewhat _more_ simplification than [simpl] does -- for
    example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    if reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    created by all this simplification and unfolding; by contrast,
    [simpl] is used in situations where we may have to read and
    understand the new goal that it creates, so we would not want it
    blindly expanding definitions and leaving the goal in a messy
    state.

    The form of the theorem we just stated and its proof are almost
    exactly the same as the simpler examples we saw earlier; there are
    just a few differences.

    First, we've used the keyword [Theorem] instead of [Example].
    This difference is mostly a matter of style; the keywords
    [Example] and [Theorem] (and a few others, including [Lemma],
    [Fact], and [Remark]) mean pretty much the same thing to Coq.

    Second, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    [n] is some number..."  Formally, this is achieved in the proof by
    [intros n], which moves [n] from the quantifier in the goal to a
    _context_ of current assumptions.

    The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    yet more in future chapters. *)

(** Other similar theorems can be proved with the same pattern. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)

(** It is worth stepping through these proofs to observe how the
    context and the goal change.  You may want to add calls to [simpl]
    before [reflexivity] to see the simplifications that Coq performs
    on the terms before checking that they are equal. *)

(* ################################################################# *)
(** * Proof by Rewriting *)

(** This theorem is a bit more interesting than the others we've
    seen: *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(** Instead of making a universal claim about all numbers [n] and [m],
    it talks about a more specialized property that only holds when [n
    = m].  The arrow symbol is pronounced "implies."

    As before, we need to be able to reason by assuming we are given such
    numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.  Qed.

(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes.) *)

(** **** 练习: .星 (plus_id_exercise)  *)
(** Remove "[Admitted.]" and fill in the proof. *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* 填空 *) Admitted.
(** [] *)

(** The [Admitted] command tells Coq that we want to skip trying
    to prove this theorem and just accept it as a given.  This can be
    useful for developing longer proofs, since we can state subsidiary
    lemmas that we believe will be useful for making some larger
    argument, use [Admitted] to accept them on faith for the moment,
    and continue working on the main argument until we are sure it
    makes sense; then we can go back and fill in the proofs we
    skipped.  Be careful, though: every time you say [Admitted] you
    are leaving a door open for total nonsense to enter Coq's nice,
    rigorous, formally checked world! *)

(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. If the statement
    of the previously proved theorem involves quantified variables,
    as in the example below, Coq tries to instantiate them
    by matching with the current goal. *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** Exercise: 2 stars (mult_S_1)  *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  (* 填空 *) Admitted.

  (* (N.b. This proof can actually be completed without using [rewrite],
     but please do use [rewrite] for the sake of the exercise.) *)
(** [] *)

(* ################################################################# *)
(** * Proof by Case Analysis *)

(** Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck.  (We then
    use the [Abort] command to give up on it for the moment.)*)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.  (* does nothing! *)
Abort.

(** The reason for this is that the definitions of both
    [beq_nat] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [beq_nat] is the compound
    expression [n + 1]; neither can be simplified.

    To make progress, we need to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [beq_nat (n + 1) 0] and check that it is, indeed, [false].  And
    if [n = S n'] for some [n'], then, although we don't know exactly
    what number [n + 1] yields, we can calculate that, at least, it
    will begin with one [S], and this is enough to calculate that,
    again, [beq_nat (n + 1) 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.   Qed.

(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem. The
    annotation "[as [| n']]" is called an _intro pattern_.  It tells
    Coq what variable names to introduce in each subgoal.  In general,
    what goes between the square brackets is a _list of lists_ of
    names, separated by [|].  In this case, the first component is
    empty, since the [O] constructor is nullary (it doesn't have any
    arguments).  The second component gives a single name, [n'], since
    [S] is a unary constructor.

    The [-] signs on the second and third lines are called _bullets_,
    and they mark the parts of the proof that correspond to each
    generated subgoal.  The proof script that comes after a bullet is
    the entire proof for a subgoal.  In this example, each of the
    subgoals is easily proved by a single use of [reflexivity], which
    itself performs some simplification -- e.g., the first one
    simplifies [beq_nat (S n' + 1) 0] to [false] by first rewriting
    [(S n' + 1)] to [S (n' + 1)], then unfolding [beq_nat], and then
    simplifying the [match].

    Marking cases with bullets is entirely optional: if bullets are
    not present, Coq simply asks you to prove each subgoal in
    sequence, one at a time. But it is a good idea to use bullets.
    For one thing, they make the structure of a proof apparent, making
    it more readable. Also, bullets instruct Coq to ensure that a
    subgoal is complete before trying to verify the next one,
    preventing proofs for different subgoals from getting mixed
    up. These issues become especially important in large
    developments, where fragile proofs lead to long debugging
    sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on one line.  Good style lies somewhere
    in the middle.  One reasonable convention is to limit yourself to
    80-character lines.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.  Qed.

(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written [as [|]], or [as []].)  In fact, we can omit the [as]
    clause from _any_ [destruct] and Coq will fill in variable names
    automatically.  This is generally considered bad style, since Coq
    often makes confusing choices of names when left to its own
    devices.

    It is sometimes useful to invoke [destruct] inside a subgoal,
    generating yet more proof obligations. In this case, we use
    different kinds of bullets to mark goals on different "levels."
    For example: *)


Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(** Each pair of calls to [reflexivity] corresponds to the
    subgoals that were generated after the execution of the [destruct c]
    line right above it. *)

(** Besides [-] and [+], we can use [*] (asterisk) as a third kind of
    bullet.  We can also enclose sub-proofs in curly braces, which is
    useful in case we ever encounter a proof that generates more than
    three levels of subgoals: *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** Since curly braces mark both the beginning and the end of a
    proof, they can be used for multiple subgoal levels, as this
    example shows. Furthermore, curly braces allow us to reuse the
    same bullet shapes at multiple levels in a proof: *)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

(** Before closing the chapter, let's mention one final convenience.  
    As you may have noticed, many proofs perform case analysis on a variable 
    right after introducing it:

       intros x y. destruct y as [|y].

    This pattern is so common that Coq provides a shorthand for it: we
    can perform case analysis on a variable when introducing it by
    using an intro pattern instead of a variable name. For instance,
    here is a shorter proof of the [plus_1_neq_0] theorem above. *)

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.

(** If there are no arguments to name, we can just write [[]]. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** **** Exercise: 2 stars (andb_true_elim2)  *)
(** Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* 填空 *) Admitted.
(** [] *)

(** **** 练习: .星 (zero_nbeq_plus_1)  *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* 填空 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** More on Notation (Optional) *)

(** (In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation definitions for infix plus and times: *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(** For each notation symbol in Coq, we can specify its _precedence
    level_ and its _associativity_.  The precedence level [n] is
    specified by writing [at level n]; this helps Coq parse compound
    expressions.  The associativity setting helps to disambiguate
    expressions containing multiple occurrences of the same
    symbol. For example, the parameters specified above for [+] and
    [*] say that the expression [1+2*3*4] is shorthand for
    [(1+((2*3)*4))]. Coq uses precedence levels from 0 to 100, and
    _left_, _right_, or _no_ associativity.  We will see more examples
    of this later, e.g., in the [Lists]
    chapter.

    Each notation symbol is also associated with a _notation scope_.
    Coq tries to guess what scope is meant from context, so when it
    sees [S(O*O)] it guesses [nat_scope], but when it sees the
    cartesian product (tuple) type [bool*bool] (which we'll see in
    later chapters) it guesses [type_scope].  Occasionally, it is
    necessary to help it out with percent-notation by writing
    [(x*y)%nat], and sometimes in what Coq prints it will use [%nat]
    to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation ([3], [4], [5],
    etc.), so you may sometimes see [0%nat], which means [O] (the
    natural number [0] that we're using in this chapter), or [0%Z],
    which means the Integer zero (which comes from a different part of
    the standard library).

    Pro tip: Coq's notation mechanism is not especially powerful.
    Don't expect too much from it! *)

(* ================================================================= *)
(** ** Fixpoints and Structural Recursion (Optional) *)

(** Here is a copy of the definition of addition: *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

(** When Coq checks this definition, it notes that [plus'] is
    "decreasing on 1st argument."  What this means is that we are
    performing a _structural recursion_ over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [plus'] will eventually
    terminate.  Coq demands that some argument of _every_ [Fixpoint]
    definition is "decreasing."

    This requirement is a fundamental feature of Coq's design: In
    particular, it guarantees that every function that can be defined
    in Coq will terminate on all inputs.  However, because Coq's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways. *)

(** **** Exercise: 2 stars, optional (decreasing)  *)
(** To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Coq will reject because
    of this restriction. *)

(* 填空 *)
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 2 stars (boolean_functions)  *)
(** Use the tactics you have learned so far to prove the following
    theorem about boolean functions. *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* 填空 *) Admitted.

(** Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x].*)

(* 填空 *)
(** [] *)

(** **** Exercise: 3 stars, optional (andb_eq_orb)  *)
(** Prove the following theorem.  (Hint: This one can be a bit tricky,
    depending on how you approach it.  You will probably need both
    [destruct] and [rewrite], but destructing everything in sight is
    not the best way.) *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* 填空 *) Admitted.

(** [] *)

(** **** Exercise: 3 stars (binary)  *)
(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) First, write an inductive definition of the type [bin]
        corresponding to this description of binary numbers.

    (Hint: Recall that the definition of [nat] above,

         Inductive nat : Type := | O : nat | S : nat -> nat.

    says nothing about what [O] and [S] "mean."  It just says "[O] is
    in the set called [nat], and if [n] is in the set then so is [S
    n]."  The interpretation of [O] as zero and [S] as successor/plus
    one comes from the way that we _use_ [nat] values, by writing
    functions to do things with them, proving things about them, and
    so on.  Your definition of [bin] should be correspondingly simple;
    it is the functions you will write next that will give it
    mathematical meaning.)

    (b) Next, write an increment function [incr] for binary numbers,
        and a function [bin_to_nat] to convert binary numbers to unary
        numbers.

    (c) Write five unit tests [test_bin_incr1], [test_bin_incr2], etc.
        for your increment and binary-to-unary functions.  (A "unit
        test" in Coq is a specific [Example] that can be proved with
        just [reflexivity], as we've done for several of our
        definitions.)  Notice that incrementing a binary number and
        then converting it to unary should yield the same result as
        first converting it to unary and then incrementing. *)

(* 填空 *)
(** [] *)

(** $Date: 2017-09-05 11:51:58 -0400 (Tue, 05 Sep 2017) $ *)

