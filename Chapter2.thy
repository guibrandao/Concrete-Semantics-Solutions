theory Chapter2 
  imports Main

begin

section\<open>Basics\<close>

subsection\<open>Types bool, nat and list\<close>

fun add:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

value "add 2 3"
value "add 10 3"


(*Exercises*)

text\<open>Exercise 1: Use the value command to evaluate the following expressions: "1+(2::nat)",
"1+(2::int)","1-(2::nat) and "1-(2::int)"\<close>

value "1+(2::nat)" 
value "1+(2::int)"
value "1-(2::nat)"
value "1-(2::int)"

text\<open>Exercise 2: Start from the definition of add given above. Prove that add is associative
and commutative. Define a recursive function double::"nat \<Rightarrow> nat" and prove double m = add m m"\<close>

theorem add_assoc [simp]: "add (add l m) n = add l (add m n)"
  apply (induction l)
   apply (auto)
  done

lemma add_suc [simp]: "add m (Suc n) = Suc (add m n)"
  apply (induction m)
   apply (auto)
  done

theorem add_comm: "add m n = add n m"
  apply (induction n)
   apply (auto)
   apply (induction m)
   apply (auto)
  done

fun double:: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc(Suc(double n))"

theorem double_add [simp]: "double n = add n n"
  apply (induction n) 
   apply auto
  done

text\<open>Exercise 3: Define a function count::"'a \<Rightarrow> 'a list \<Rightarrow> nat" that counts the number of
occurrences of an element in a list. Prove count x xs \<le> length xs.\<close>

fun count:: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x Nil = 0" |
"count x (Cons a xs) = (if x=a then 1 + count x xs else (count x xs))"

value "count (5::int) [1,2,5,4,5,5,6,7]"
value "count (x:: 'a) [x,y,s,x,t,x]"

theorem count_length: "count x xs \<le> length xs"
  apply (induction xs)
   apply (auto)
  done

text\<open>Exercise 4: Define a recursive function snoc::"'a list \<Rightarrow> 'a  \<Rightarrow> 'a list" that appends 
an element to the end of a list. With the help of snoc define a recursive function
reverse:: "'a list \<Rightarrow> 'a list" that reverses a list. Prove that reverse (reverse xs) = xs.\<close>

fun snoc::"'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil x = (Cons x Nil)" |
"snoc (Cons a xs) x = Cons a (snoc xs x)"

value "snoc ([5,4,3,2]:: nat list) 1"

fun reverse:: "'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil" |
"reverse (Cons x xs) = snoc (reverse xs) x"

value "reverse ([5,4,3,2,1]:: nat list)"

lemma reverse_snoc [simp]: "reverse (snoc xs x) = Cons x (reverse xs)"
  apply (induction xs)
   apply (auto)
  done

theorem reverse_reverse [simp]: "reverse (reverse xs) = xs"
  apply (induction xs)
   apply (auto)
  done

text\<open>Exercise 5: Define a recursive function sum_upto:: "nat \<Rightarrow> nat" such that 
sum_upto n = 0 + 1 + \<dots> + n" and prove sum_upto n = n*(n+1)/2.\<close>

fun sum_upto:: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0"|
"sum_upto (Suc n) = Suc n + sum_upto n"

theorem gauss_sum [simp]: "sum_upto n = (n*(n+1)) div 2"
  apply (induction n)
   apply (auto)
  done


subsection\<open>Type and Function definitions\<close>

datatype 'a tree = Tip
  | Node "'a tree" 'a "'a tree"

fun mirror:: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip"
| "mirror (Node t1 x t2) = Node (mirror t1) x (mirror t2)"

text\<open>Exercise 6: Starting from the type 'a tree defined in the text, define a function 
contents:: "'a tree \<Rightarrow> 'a list" that collects all the values in a tree in a list, in any
order, without removing duplicates. Then, define a function sum_tree:: "nat tree \<Rightarrow> nat" that
sums up all the variables in a tree of natural numbers and prove sum_tree t = sum_list(contents t)
where sum_list is predefined by the equations sum_list[]=0 and sum_list=x#xs=x+sum_list xs.\<close>

fun contents:: "'a tree \<Rightarrow> 'a list" where
"contents Tip  = Nil"
| "contents (Node t1 x t2) =  Cons x (contents t1)@(contents t2)"

fun sum_tree:: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0"
| "sum_tree (Node t1 x t2) = x + sum_tree(t1) + sum_tree(t2)"

theorem sum_tree_eq_sum_list: "sum_tree t = sum_list(contents t)"
  apply(induction t)
   apply (auto)
  done

text\<open>Exercise 7: Define the two functions pre_order:: "'a tree \<Rightarrow> 'a list" and post_order::"'a tree 
\<Rightarrow> 'a list" that traverse a tree and collect all stored values in the respective order in a list.
Prove that pre_order(mirror t)=rev(post_order t)\<close>

datatype 'a tree2 = Tip 'a
  | Node "'a tree2" 'a "'a tree2"

fun mirror2:: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Tip a) = Tip a"
| "mirror2 (Node t1 x t2) = Node (mirror2 t2) x (mirror2 t1)"

fun pre_order:: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip a) = Cons a Nil"
| "pre_order (Node t1 x t2) = (Cons x (pre_order t1)) @ (pre_order t2)"

fun post_order:: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip a) = Cons a Nil"
| "post_order (Node t1 x t2) = ((post_order t1)@(post_order t2))@[x]"

theorem preorder_postorder: "pre_order (mirror2 t) = rev(post_order t)"
  apply (induction t)
   apply (auto)
  done

text\<open>Exercise 8: Define a function intersperse:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" such that
intersperse a [x_1,\<dots>,x_n]=[x_1,a,x_2,a,\<dots>,a,x_n]. Then prove that
map f (intersperse a xs) = intersperse (f a) (map f xs).\<close>

fun intersperse:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a Nil = Nil"
| "intersperse a [x] = [x]"
| "intersperse a (Cons x xs) = x # a # (intersperse a xs)"

theorem interperse_map: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  apply (auto)
  done

text\<open>Exercise 9: Write a tail-recursive variant of the add function on nat: itadd. Tail-recursive 
means that in the recursive case, itadd needs to call itself directly: 
itadd (Suc m) n = itadd... .Prove itadd m n = add m n.\<close>

fun itadd:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_suc: "itadd m (Suc n) = add (Suc m) n"
  apply (induction m arbitrary: n)
   apply (auto)
  done

theorem itadd_equals_add: "itadd m n = add m n"
  apply (induction m)
   apply (auto simp add: itadd_suc)
  done

text\<open>Exercise 10: Define a datatype tree0 of binary tree skeletons which do not store any
information, neither in the inner nodes nor in the leaves. Define a function nodes:: tree0 \<Rightarrow> nat
that counts the number of all nodes (inner nodes and leaves in such a tree. Consider the following
recursive function:

fun explode:: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t"
| "explode (Suc n) t = explode n (Node t t)"

Find an equation expressing the size of a tree after exploding it (nodes (explode n t)) as a
function of nodes t and n. Prove your equation. You may use the usual arithmetic operators, 
including the exponential operator "^". For example:  2^2=4.

Hint: simplifying with the list of of theorems algebra_simps takes care of common algebraic pro-
perties of algebraic operators.\<close>

datatype tree0 = Tip
  | Node "tree0" "tree0"

fun nodes:: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1"
| "nodes (Node t1 t2) = 1 + nodes t1 + nodes t2"

fun explode:: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t"
| "explode (Suc n) t = explode n (Node t t)"

thm algebra_simps

theorem size_explosion: "nodes (explode n t) = 2^n * nodes t + 2^n - 1"
  apply (induction n arbitrary: t)
   apply (auto simp add: algebra_simps)
  done

text\<open>Exercise 11: Define arithmetic expressions in one variable over integers (type int) as a 
datatype

datatype exp = Var | Const int | Add exp exp | Mult exp exp

Define a function eval:: exp \<Rightarrow> int \<Rightarrow> int such that eval e x evaluates e at the value x.

A polynomial can be represented as a list of coefficients, starting with the constant. For example,
[4,2,-1,3] represents the polynomial 4+2x-x^2+3x^3. Define a function evalp:: int list \<Rightarrow> int 
\<Rightarrow> int that evaluates a polynomial at the given value. Define a function coeffs:: exp \<Rightarrow> int list
that transforms an expression into a polynomial. This may require auxiliary functions. Prove that
coeffs preserves the value of the expression: evalp (coeffs e) x = eval e x.

Hint: consider the hint in exercise 10.\<close>

datatype exp = Var 
  | Const int 
  | Add exp exp 
  | Mult exp exp

fun eval:: "exp \<Rightarrow> int \<Rightarrow> int" where 
"eval Var x = x"
| "eval (Const c) x = c"
| "eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)"
| "eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp:: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp Nil x = 0" |
"evalp (t # ts) x = t + x*(evalp ts x)"




end
