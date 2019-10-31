# Math Notes

## Bibliography

\[Stoll56] Robert R. Stoll. _Linear Algebra & Matrix Theory_

### PART 1  CLASSICAL FIRST-ORDER LOGIC WITH EQUALITY

#### 1.1  Pre-logic

##### 1.1.1  Inferences for assisting proof development   dummylink 1

#### 1.2  Propositional calculus

##### 1.2.1  Recursively define primitive wffs for propositional calculus   wn 3

##### 1.2.2  The axioms of propositional calculus   ax-mp 5

##### 1.2.3  Logical implication   mp2 9

##### 1.2.4  Logical negation   con4d 105

##### 1.2.5  Logical equivalence   wb 184

##### 1.2.6  Logical disjunction and conjunction   wo 368

##### 1.2.7  Miscellaneous theorems of propositional calculus   pm5.21nd 886

##### 1.2.8  Abbreviated conjunction and disjunction of three wff's   w3o 957

##### 1.2.9  Logical 'nand' (Sheffer stroke)   wnan 1326

##### 1.2.10  Logical 'xor'   wxo 1343

##### 1.2.11  True and false constants   wal 1360

###### 1.2.11.1  Universal quantifier for use by df-tru   wal 1360

###### 1.2.11.2  Equality predicate for use by df-tru   cv 1361

###### 1.2.11.3  Define the true and false constants   wtru 1363

##### 1.2.12  Truth tables   truantru 1386

##### 1.2.13  Auxiliary theorems for Alan Sare's virtual deduction tool   exbir 1412

##### 1.2.14  Half-adders and full adders in propositional calculus   whad 1422

#### 1.3  Other axiomatizations of classical propositional calculus

##### 1.3.1  Derive the Lukasiewicz axioms from Meredith's sole axiom   meredith 1449

##### 1.3.2  Derive the standard axioms from the Lukasiewicz axioms   luklem1 1468

##### 1.3.3  Derive Nicod's axiom from the standard axioms   nic-dfim 1479

##### 1.3.4  Derive the Lukasiewicz axioms from Nicod's axiom   nic-imp 1485

##### 1.3.5  Derive Nicod's Axiom from Lukasiewicz's First Sheffer Stroke Axiom   lukshef-ax1 1504

##### 1.3.6  Derive the Lukasiewicz Axioms from the Tarski-Bernays-Wajsberg Axioms   tbw-bijust 1508

##### 1.3.7  Derive the Tarski-Bernays-Wajsberg axioms from Meredith's First CO Axiom   merco1 1523

##### 1.3.8  Derive the Tarski-Bernays-Wajsberg axioms from Meredith's Second CO Axiom   merco2 1546

##### 1.3.9  Derive the Lukasiewicz axioms from the Russell-Bernays Axioms   rb-bijust 1559

##### 1.3.10  Stoic logic non-modal portion (Chrysippus of Soli)   mptnan 1578

#### 1.4  Predicate calculus with equality: Tarski's system S2 (1 rule, 6 schemes)

##### 1.4.1  Universal quantifier (continued); define "exists" and "not free"   wex 1589

##### 1.4.2  Rule scheme ax-gen (Generalization)   ax-gen 1594

##### 1.4.3  Axiom scheme ax-4 (Quantified Implication)   ax-4 1605

##### 1.4.4  Axiom scheme ax-5 (Distinctness) - first use of $d   ax-5 1669

##### 1.4.5  Equality predicate (continued)   weq 1694

##### 1.4.6  Define proper substitution   wsb 1699

##### 1.4.7  Axiom scheme ax-6 (Existence)   ax-6 1707

##### 1.4.8  Axiom scheme ax-7 (Equality)   ax-7 1727

##### 1.4.9  Membership predicate   wcel 1755

##### 1.4.10  Axiom scheme ax-8 (Left Equality for Binary Predicate)   ax-8 1757

##### 1.4.11  Axiom scheme ax-9 (Right Equality for Binary Predicate)   ax-9 1759

##### 1.4.12  Logical redundancy of ax-10 , ax-11 , ax-12 , ax-13   ax6dgen 1761

#### 1.5  Predicate calculus with equality: Auxiliary axiom schemes (4 schemes)

##### 1.5.1  Axiom scheme ax-10 (Quantified Negation)   ax-10 1774

##### 1.5.2  Axiom scheme ax-11 (Quantifier Commutation)   ax-11 1779

##### 1.5.3  Axiom scheme ax-12 (Substitution)   ax-12 1791

##### 1.5.4  Axiom scheme ax-13 (Quantified Equality)   ax-13 1942

#### 1.6  Predicate calculus with equality: Older axiomatization (1 rule, 14 schemes)

##### 1.6.1  Obsolete schemes ax-c4,c5,c7,c10,c11,c11n,c15,c9,c14,c16   ax-c5 2186

##### 1.6.2  Rederive new axioms from old: ax4 , ax10 , ax6fromc10 , ax12 , ax13fromc9   axc5 2196

##### 1.6.3  Legacy theorems using obsolete axioms   ax5ALT 2208

#### 1.7  Existential uniqueness

#### 1.8  Other axiomatizations related to classical predicate calculus

##### 1.8.1  Predicate calculus with all distinct variables   ax-7d 2369

##### 1.8.2  Aristotelian logic: Assertic syllogisms   barbara 2375

##### 1.8.3  Intuitionistic logic   axia1 2399

### PART 2  ZF (ZERMELO-FRAENKEL) SET THEORY

#### 2.1  ZF Set Theory - start with the Axiom of Extensionality

##### 2.1.1  Introduce the Axiom of Extensionality   ax-ext 2414

Axiom of Extensionality. An axiom of Zermelo-Fraenkel set theory. It states that two sets are identical if they contain the same elements. ax-ext 2414

⊢ (∀𝑧(𝑧 ∈ 𝑥 ↔ 𝑧 ∈ 𝑦) → 𝑥 = 𝑦)

##### 2.1.2  Class abstractions (a.k.a. class builders)   cab 2419

Define the equality connective between classes. df-cleq 2426

⊢ (∀𝑥(𝑥 ∈ 𝑦 ↔ 𝑥 ∈ 𝑧) → 𝑦 = 𝑧)    ⇒   ⊢ (𝐴 = 𝐵 ↔ ∀𝑥(𝑥 ∈ 𝐴 ↔ 𝑥 ∈ 𝐵))

Transitive law for class equality. eqtr3 2452

⊢ ((𝐴 = 𝐶 ∧ 𝐵 = 𝐶) → 𝐴 = 𝐵)

##### 2.1.3  Class form not-free predicate   wnfc 2556

##### 2.1.4  Negated equality and membership   wne 2596

###### 2.1.4.1  Negated equality   neii 2600

###### 2.1.4.2  Negated membership   neli 2697

##### 2.1.5  Restricted quantification   wral 2705

##### 2.1.6  The universal class   cvv 2962

##### 2.1.7  Conditional equality (experimental)   wcdeq 3158

##### 2.1.8  Russell's Paradox   ru 3174

##### 2.1.9  Proper substitution of classes for sets   wsbc 3175

##### 2.1.10  Proper substitution of classes for sets into classes   csb 3276

##### 2.1.11  Define basic set operations and relations   cdif 3313

Define the intersection of two classes. df-in 3323

⊢ (𝐴 ∩ 𝐵) = {𝑥 ∣ (𝑥 ∈ 𝐴 ∧ 𝑥 ∈ 𝐵)}

##### 2.1.12  Subclasses and subsets   df-ss 3330

Define proper subclass relationship between two classes. df-pss 3332

⊢ (𝐴 ⊊ 𝐵 ↔ (𝐴 ⊆ 𝐵 ∧ 𝐴 ≠ 𝐵))

Alternate definition of subclass relationship. dfss3 3334*

⊢ (𝐴 ⊆ 𝐵 ↔ ∀𝑥 ∈ 𝐴 𝑥 ∈ 𝐵)

The subclass relationship is antisymmetric. eqss 3359

⊢ (𝐴 = 𝐵 ↔ (𝐴 ⊆ 𝐵 ∧ 𝐵 ⊆ 𝐴))

bq. The equality of two sets S and T, written S = T, is synonymous with S ⊆ T and S ⊇ T. [Stoll56], p. xiii


Alternate definition of proper subclass. dfpss2 3429

⊢ (𝐴 ⊊ 𝐵 ↔ (𝐴 ⊆ 𝐵 ∧ ¬ 𝐴 = 𝐵))

Alternate definition of proper subclass. dfpss3 3430

⊢ (𝐴 ⊊ 𝐵 ↔ (𝐴 ⊆ 𝐵 ∧ ¬ 𝐵 ⊆ 𝐴))


##### 2.1.13  The difference, union, and intersection of two classes   difeq1 3455

###### 2.1.13.1  The difference of two classes   difeq1 3455

###### 2.1.13.2  The union of two classes   elun 3485

###### 2.1.13.3  The intersection of two classes   elin 3527

Expansion of membership in an intersection of two classes. elin 3527

⊢ (𝐴 ∈ (𝐵 ∩ 𝐶) ↔ (𝐴 ∈ 𝐵 ∧ 𝐴 ∈ 𝐶))


###### 2.1.13.4  Combinations of difference, union, and intersection of two classes   unabs 3568

###### 2.1.13.5  Class abstractions with difference, union, and intersection of two classes   symdif2 3604

###### 2.1.13.6  Restricted uniqueness with difference, union, and intersection   reuss2 3618

##### 2.1.14  The empty set   c0 3625

A nonempty class has at least one element. neq0 3635

⊢ (¬ 𝐴 = ∅ ↔ ∃𝑥 𝑥 ∈ 𝐴)

The empty set has no elements. eq0 3640

⊢ (𝐴 = ∅ ↔ ∀𝑥 ¬ 𝑥 ∈ 𝐴)

Two ways of saying that two classes are disjoint (have no members in common). disj 3707

⊢ ((𝐴 ∩ 𝐵) = ∅ ↔ ∀𝑥 ∈ 𝐴 ¬ 𝑥 ∈ 𝐵)

A proper subclass has a member in one argument that's not in both. pssnel 3732

⊢ (𝐴 ⊊ 𝐵 → ∃𝑥(𝑥 ∈ 𝐵 ∧ ¬ 𝑥 ∈ 𝐴))

A subclass missing a member is a proper subclass. ssnelpss 3730

⊢ (𝐴 ⊆ 𝐵 → ((𝐶 ∈ 𝐵 ∧ ¬ 𝐶 ∈ 𝐴) → 𝐴 ⊊ 𝐵))

bq. If T contains S and also elements not in S, we say that T contains S properly, written: T ⊃ S or that S is a proper subset of T, written S ⊂ T. [Stoll56], p. xiii


##### 2.1.15  "Weak deduction theorem" for set theory   cif 3779

##### 2.1.16  Power classes   cpw 3848

##### 2.1.17  Unordered and ordered pairs   snjust 3864

Define the singleton of a class. df-sn 3866

⊢ {𝐴} = {𝑥 ∣ 𝑥 = 𝐴}

Define unordered pair of classes. df-pr 3868

⊢ {𝐴, 𝐵} = ({𝐴} ∪ {𝐵})

Define unordered triple of classes. df-tp 3870

⊢ {𝐴, 𝐵, 𝐶} = ({𝐴, 𝐵} ∪ {𝐶})

##### 2.1.18  The union of a class   cuni 4079

##### 2.1.19  The intersection of a class   cint 4116

##### 2.1.20  Indexed union and intersection   ciun 4159

##### 2.1.21  Disjointness   wdisj 4250

##### 2.1.22  Binary relations   wbr 4280

##### 2.1.23  Ordered-pair class abstractions (class builders)   copab 4337

##### 2.1.24  Transitive classes   wtr 4373

#### 2.2  ZF Set Theory - add the Axiom of Replacement

##### 2.2.1  Introduce the Axiom of Replacement   ax-rep 4391

##### 2.2.2  Derive the Axiom of Separation   axsep 4400

##### 2.2.3  Derive the Null Set Axiom   zfnuleu 4406

The Null Set Axiom of ZF set theory: the empty set exists. 0ex 4410

⊢ ∅ ∈ V

bq. If S and T have no elements in common, we say that S ∩ T is empty. We agree to speak  of an empty set as one containing no elements and, moreover, that there is only one empty set. A set containing at least one element is called nonempty. [Stoll56], p. xiii

##### 2.2.4  Theorems requiring subset and intersection existence   nalset 4417

Separation Scheme (Aussonderung) using class notation. inex1 4421	

⊢ 𝐴 ∈ V    ⇒   ⊢ (𝐴 ∩ 𝐵) ∈ V

bq. The set R, consisting of all elements common to two given sets S and T is called the intersection of S and T; in symbols: R = S ∩ T . [Stoll56], p. xiii

The subset of a set is also a set. ssex 4424

⊢ 𝐵 ∈ V    ⇒   ⊢ (𝐴 ⊆ 𝐵 → 𝐴 ∈ V)

bq. If all elements of a set S are elements of a set T, we call S a subset of T and say S is contained in T; in symbols: S ⊆ T .  We may also say T contains S under these circumstances; in symbols: T ⊇ S . [Stoll56], p. xiii

##### 2.2.5  Theorems requiring empty set existence   class2set 4447

#### 2.3  ZF Set Theory - add the Axiom of Power Sets

##### 2.3.1  Introduce the Axiom of Power Sets   ax-pow 4458

##### 2.3.2  Derive the Axiom of Pairing   zfpair 4517

A singleton is a set. snex 4521

⊢ {𝐴} ∈ V

The Axiom of Pairing using class variables. prex 4522

⊢ {𝐴, 𝐵} ∈ V

##### 2.3.3  Ordered pair theorem   opnz 4551

##### 2.3.4  Ordered-pair class abstractions (cont.)   opabid 4584

##### 2.3.5  Power class of union and intersection   pwin 4612

##### 2.3.6  Epsilon and identity relations   cep 4617

##### 2.3.7  Partial and complete ordering   wpo 4626

##### 2.3.8  Founded and well-ordering relations   wfr 4663

##### 2.3.9  Ordinals   word 4705

##### 2.3.10  Relations   cxp 4825

##### 2.3.11  Definite description binder (inverted iota)   cio 5367

##### 2.3.12  Functions   wfun 5400

##### 2.3.13  Cantor's Theorem   canth 6036

##### 2.3.14  Restricted iota (description binder)   crio 6038

##### 2.3.15  Operations   co 6080

##### 2.3.16  "Maps to" notation   elmpt2cl 6293

##### 2.3.17  Function operation   cof 6307

##### 2.3.18  Proper subset relation   crpss 6348

#### 2.4  ZF Set Theory - add the Axiom of Union

##### 2.4.1  Introduce the Axiom of Union   ax-un 6361

A triple of classes exists. tpex 6368

⊢ { 𝐴 , 𝐵 , 𝐶 } ∈ V

bq. Without exception {a, b, c, ... } is symbolism for the phrase “the set whose members (or elements), without regard to order, are a, b, c, ... .” [Stoll56], p. xiii


##### 2.4.2  Ordinals (continued)   ordon 6383

##### 2.4.3  Transfinite induction   tfi 6453

##### 2.4.4  The natural numbers (i.e. finite ordinals)   com 6465

##### 2.4.5  Peano's postulates   peano1 6484

##### 2.4.6  Finite induction (for finite ordinals)   find 6490

##### 2.4.7  First and second members of an ordered pair   c1st 6564

##### 2.4.8  The support of functions   csupp 6679

##### 2.4.9  Special "Maps to" operations   mpt2xopn0yelv 6719

##### 2.4.10  Function transposition   ctpos 6733

##### 2.4.11  Curry and uncurry   ccur 6773

##### 2.4.12  Undefined values   cund 6777

##### 2.4.13  Functions on ordinals; strictly monotone ordinal functions   iunon 6785

##### 2.4.14  "Strong" transfinite recursion   crecs 6817

##### 2.4.15  Recursive definition generator   crdg 6851

##### 2.4.16  Finite recursion   frfnom 6876

##### 2.4.17  Abian's "most fundamental" fixed point theorem   abianfplem 6899

##### 2.4.18  Ordinal arithmetic   c1o 6901

##### 2.4.19  Natural number arithmetic   nna0 7031

##### 2.4.20  Equivalence relations and classes   wer 7086

##### 2.4.21  The mapping operation   cmap 7202

##### 2.4.22  Infinite Cartesian products   cixp 7251

##### 2.4.23  Equinumerosity   cen 7295

##### 2.4.24  Schroeder-Bernstein Theorem   sbthlem1 7409

##### 2.4.25  Equinumerosity (cont.)   xpf1o 7461

##### 2.4.26  Pigeonhole Principle   phplem1 7478

##### 2.4.27  Finite sets   onomeneq 7488

##### 2.4.28  Finitely supported functions   cfsupp 7608

##### 2.4.29  Finite intersections   cfi 7648

##### 2.4.30  Hall's marriage theorem   marypha1lem 7671

##### 2.4.31  Supremum   csup 7678

##### 2.4.32  Ordinal isomorphism, Hartog's theorem   coi 7711

##### 2.4.33  Hartogs function, order types, weak dominance   char 7759

#### 2.5  ZF Set Theory - add the Axiom of Regularity

##### 2.5.1  Introduce the Axiom of Regularity   ax-reg 7795

##### 2.5.2  Axiom of Infinity equivalents   inf0 7815

#### 2.6  ZF Set Theory - add the Axiom of Infinity

##### 2.6.1  Introduce the Axiom of Infinity   ax-inf 7832

##### 2.6.2  Existence of omega (the set of natural numbers)   omex 7837

##### 2.6.3  Cantor normal form   ccnf 7855

##### 2.6.4  Transitive closure   trcl 7936

##### 2.6.5  Rank   cr1 7957

##### 2.6.6  Scott's trick; collection principle; Hilbert's epsilon   scottex 8080

##### 2.6.7  Cardinal numbers   ccrd 8093

##### 2.6.8  Axiom of Choice equivalents   wac 8273

##### 2.6.9  Cardinal number arithmetic   ccda 8324

##### 2.6.10  The Ackermann bijection   ackbij2lem1 8376

##### 2.6.11  Cofinality (without Axiom of Choice)   cflem 8403

##### 2.6.12  Eight inequivalent definitions of finite set   sornom 8434

##### 2.6.13  Hereditarily size-limited sets without Choice   itunifval 8573

### PART 3  ZFC (ZERMELO-FRAENKEL WITH CHOICE) SET THEORY

#### 3.1  ZFC Set Theory - add Countable Choice and Dependent Choice

##### 3.1.1  Introduce the Axiom of Countable Choice   ax-cc 8592

##### 3.1.2  Introduce the Axiom of Dependent Choice   ax-dc 8603

#### 3.2  ZFC Set Theory - add the Axiom of Choice

##### 3.2.1  Introduce the Axiom of Choice   ax-ac 8616

##### 3.2.2  AC equivalents: well-ordering, Zorn's lemma   numthcor 8651

##### 3.2.3  Cardinal number theorems using Axiom of Choice   cardval 8698

##### 3.2.4  Cardinal number arithmetic using Axiom of Choice   iunctb 8726

##### 3.2.5  Cofinality using Axiom of Choice   alephreg 8734

#### 3.3  ZFC Axioms with no distinct variable requirements

#### 3.4  The Generalized Continuum Hypothesis

##### 3.4.1  Sets satisfying the Generalized Continuum Hypothesis   cgch 8774

##### 3.4.2  Derivation of the Axiom of Choice   gchaclem 8832

### PART 4  TG (TARSKI-GROTHENDIECK) SET THEORY

#### 4.1  Inaccessibles

##### 4.1.1  Weakly and strongly inaccessible cardinals   cwina 8836

##### 4.1.2  Weak universes   cwun 8854

##### 4.1.3  Tarski classes   ctsk 8902

##### 4.1.4  Grothendieck universes   cgru 8944

#### 4.2  ZFC Set Theory plus the Tarski-Grothendieck Axiom

##### 4.2.1  Introduce the Tarski-Grothendieck Axiom   ax-groth 8977

##### 4.2.2  Derive the Power Set, Infinity and Choice Axioms   grothpw 8980

##### 4.2.3  Tarski map function   ctskm 8991

### PART 5  REAL AND COMPLEX NUMBERS

#### 5.1  Construction and axiomatization of real and complex numbers

##### 5.1.1  Dedekind-cut construction of real and complex numbers   cnpi 8998

##### 5.1.2  Final derivation of real and complex number postulates   axaddf 9299

##### 5.1.3  Real and complex number postulates restated as axioms   ax-cnex 9325

#### 5.2  Derive the basic properties from the field axioms

##### 5.2.1  Some deductions from the field axioms for complex numbers   cnex 9350

##### 5.2.2  Infinity and the extended real number system   cpnf 9402

##### 5.2.3  Restate the ordering postulates with extended real "less than"   axlttri 9433

##### 5.2.4  Ordering on reals   lttr 9438

##### 5.2.5  Initial properties of the complex numbers   mul12 9522

#### 5.3  Real and complex numbers - basic operations

##### 5.3.1  Addition   add12 9569

##### 5.3.2  Subtraction   cmin 9582

##### 5.3.3  Multiplication   muladd 9764

##### 5.3.4  Ordering on reals (cont.)   gt0ne0 9791

##### 5.3.5  Reciprocals   ixi 9952

##### 5.3.6  Division   cdiv 9980

##### 5.3.7  Ordering on reals (cont.)   elimgt0 10152

##### 5.3.8  Completeness Axiom and Suprema   fimaxre 10264

##### 5.3.9  Imaginary and complex number properties   inelr 10299

##### 5.3.10  Function operation analogue theorems   ofsubeq0 10306

#### 5.4  Integer sets

##### 5.4.1  Positive integers (as a subset of complex numbers)   cn 10309

##### 5.4.2  Principle of mathematical induction   nnind 10327

##### 5.4.3  Decimal representation of numbers   c2 10358

##### 5.4.4  Some properties of specific numbers   neg1cn 10412

##### 5.4.5  Simple number properties   halfcl 10537

##### 5.4.6  The Archimedean property   nnunb 10562

##### 5.4.7  Nonnegative integers (as a subset of complex numbers)   cn0 10566

##### 5.4.8  Integers (as a subset of complex numbers)   cz 10633

##### 5.4.9  Decimal arithmetic   cdc 10742

##### 5.4.10  Upper sets of integers   cuz 10848

##### 5.4.11  Well-ordering principle for bounded-below sets of integers   uzwo3 10935

##### 5.4.12  Rational numbers (as a subset of complex numbers)   cq 10940

##### 5.4.13  Existence of the set of complex numbers   rpnnen1lem1 10966

#### 5.5  Order sets

##### 5.5.1  Positive reals (as a subset of complex numbers)   crp 10978

##### 5.5.2  Infinity and the extended real number system (cont.)   cxne 11073

##### 5.5.3  Supremum on the extended reals   xrsupexmnf 11254

##### 5.5.4  Real number intervals   cioo 11287

##### 5.5.5  Finite intervals of integers   cfz 11423

##### 5.5.6  Half-open integer ranges   cfzo 11531

#### 5.6  Elementary integer functions

##### 5.6.1  The floor and ceiling functions   cfl 11623

##### 5.6.2  The modulo (remainder) operation   cmo 11691

##### 5.6.3  The infinite sequence builder "seq"   om2uz0i 11753

##### 5.6.4  Integer powers   cexp 11848

##### 5.6.5  Ordered pair theorem for nonnegative integers   nn0le2msqi 12028

##### 5.6.6  Factorial function   cfa 12034

##### 5.6.7  The binomial coefficient operation   cbc 12061

##### 5.6.8  The ` # ` (finite set size) function   chash 12086

###### 5.6.8.1  Finite induction on the size of the first component of a binary relation   brfi1indlem 12201

#### 5.7  Words over a set

##### 5.7.1  Definitions and basic theorems   cword 12204

##### 5.7.2  Last symbol of a word   lsw 12249

##### 5.7.3  Concatenations of words   ccatfn 12255

##### 5.7.4  Singleton words   ids1 12272

##### 5.7.5  Concatenations with singleton words   ccatws1cl 12286

##### 5.7.6  Subwords   swrdval 12296

##### 5.7.7  Subwords of subwords   swrdswrdlem 12336

##### 5.7.8  Subwords and concatenations   wrdcctswrd 12342

##### 5.7.9  Subwords of concatenations   swrdccatfn 12356

##### 5.7.10  Splicing words (substring replacement)   splval 12376

##### 5.7.11  Reversing words   revval 12383

##### 5.7.12  Repeated symbol words   reps 12391

##### 5.7.13  Cyclical shifts of words   ccsh 12408

##### 5.7.14  Mapping words by a function   wrdco 12442

##### 5.7.15  Longer string literals   cs2 12451

#### 5.8  Elementary real and complex functions

##### 5.8.1  The "shift" operation   cshi 12538

##### 5.8.2  Signum (sgn or sign) function   csgn 12558

##### 5.8.3  Real and imaginary parts; conjugate   ccj 12568

##### 5.8.4  Square root; absolute value   csqr 12705

#### 5.9  Elementary limits and convergence

##### 5.9.1  Superior limit (lim sup)   clsp 12931

##### 5.9.2  Limits   cli 12945

##### 5.9.3  Finite and infinite sums   csu 13146

Combine two sums into a single sum over the cartesian product. fsumxp 13222

⊢ (𝑧 = ⟨𝑗, 𝑘⟩ → 𝐷 = 𝐶)
	&   ⊢ (𝜑 → 𝐴 ∈ Fin)
	&   ⊢ (𝜑 → 𝐵 ∈ Fin)
	&   ⊢ ((𝜑 ∧ (𝑗 ∈ 𝐴 ∧ 𝑘 ∈ 𝐵)) → 𝐶 ∈ ℂ)
	⇒   ⊢ (𝜑 → Σ𝑗 ∈ 𝐴 Σ𝑘 ∈ 𝐵 𝐶 = Σ𝑧 ∈ (𝐴 × 𝐵)𝐷)

Interchange order of summation. Note that 𝐵(𝑗) and 𝐷(𝑘) are not necessarily constant expressions. fsumcom2 13224

⊢ (𝜑 → 𝐴 ∈ Fin)
	&   ⊢ (𝜑 → 𝐶 ∈ Fin)
	&   ⊢ ((𝜑 ∧ 𝑗 ∈ 𝐴) → 𝐵 ∈ Fin)
	&   ⊢ (𝜑 → ((𝑗 ∈ 𝐴 ∧ 𝑘 ∈ 𝐵) ↔ (𝑘 ∈ 𝐶 ∧ 𝑗 ∈ 𝐷)))
	&   ⊢ ((𝜑 ∧ (𝑗 ∈ 𝐴 ∧ 𝑘 ∈ 𝐵)) → 𝐸 ∈ ℂ)
	⇒   ⊢ (𝜑 → Σ𝑗 ∈ 𝐴 Σ𝑘 ∈ 𝐵 𝐸 = Σ𝑘 ∈ 𝐶 Σ𝑗 ∈ 𝐷 𝐸)

Interchange order of summation. fsumcom 13225

⊢ (𝜑 → 𝐴 ∈ Fin)
	&   ⊢ (𝜑 → 𝐵 ∈ Fin)
	&   ⊢ ((𝜑 ∧ (𝑗 ∈ 𝐴 ∧ 𝑘 ∈ 𝐵)) → 𝐶 ∈ ℂ)
	⇒   ⊢ (𝜑 → Σ𝑗 ∈ 𝐴 Σ𝑘 ∈ 𝐵 𝐶 = Σ𝑘 ∈ 𝐵 Σ𝑗 ∈ 𝐴 𝐶)

See [Stoll56], p. xiv


##### 5.9.4  The binomial theorem   binomlem 13274

##### 5.9.5  The inclusion/exclusion principle   incexclem 13281

##### 5.9.6  Infinite sums (cont.)   isumshft 13284

##### 5.9.7  Miscellaneous converging and diverging sequences   divrcnv 13297

##### 5.9.8  Arithmetic series   arisum 13304

##### 5.9.9  Geometric series   expcnv 13308

##### 5.9.10  Ratio test for infinite series convergence   cvgrat 13325

##### 5.9.11  Mertens' theorem   mertenslem1 13326

#### 5.10  Elementary trigonometry

##### 5.10.1  The exponential, sine, and cosine functions   ce 13329

##### 5.10.2  _e is irrational   eirrlem 13468

#### 5.11  Cardinality of real and complex number subsets

##### 5.11.1  Countability of integers and rationals   xpnnen 13473

##### 5.11.2  The reals are uncountable   rpnnen2lem1 13479

### PART 6  ELEMENTARY NUMBER THEORY

#### 6.1  Elementary properties of divisibility

##### 6.1.1  Irrationality of square root of 2   sqr2irrlem 13512

##### 6.1.2  Some Number sets are chains of proper subsets   nthruc 13515

##### 6.1.3  The divides relation   cdivides 13517

##### 6.1.4  The division algorithm   divalglem0 13579

##### 6.1.5  Bit sequences   cbits 13597

##### 6.1.6  The greatest common divisor operator   cgcd 13672

##### 6.1.7  Bézout's identity   bezoutlem1 13704

##### 6.1.8  Algorithms   nn0seqcvgd 13727

##### 6.1.9  Euclid's Algorithm   eucalgval2 13738

#### 6.2  Elementary prime number theory

##### 6.2.1  Elementary properties   cprime 13745

##### 6.2.2  Properties of the canonical representation of a rational   cnumer 13793

##### 6.2.3  Euler's theorem   codz 13820

##### 6.2.4  Arithmetic modulo a prime number   modprm1div 13851

##### 6.2.5  Pythagorean Triples   coprimeprodsq 13858

##### 6.2.6  The prime count function   cpc 13885

##### 6.2.7  Pocklington's theorem   prmpwdvds 13947

##### 6.2.8  Infinite primes theorem   unbenlem 13951

##### 6.2.9  Sum of prime reciprocals   prmreclem1 13959

##### 6.2.10  Fundamental theorem of arithmetic   1arithlem1 13966

##### 6.2.11  Lagrange's four-square theorem   cgz 13972

##### 6.2.12  Van der Waerden's theorem   cvdwa 14008

##### 6.2.13  Ramsey's theorem   cram 14042

##### 6.2.14  Decimal arithmetic (cont.)   dec2dvds 14074

##### 6.2.15  Cyclical shifts of words (cont.)   cshwsidrepsw 14102

##### 6.2.16  Specific prime numbers   4nprm 14114

##### 6.2.17  Very large primes   1259lem1 14137

### PART 7  BASIC STRUCTURES

#### 7.1  Extensible structures

##### 7.1.1  Basic definitions   cstr 14152

##### 7.1.2  Slot definitions   cplusg 14220

##### 7.1.3  Definition of the structure product   crest 14341

##### 7.1.4  Definition of the structure quotient   cordt 14419

#### 7.2  Moore spaces

##### 7.2.1  Moore closures   mrcflem 14526

##### 7.2.2  Independent sets in a Moore system   mrisval 14550

##### 7.2.3  Algebraic closure systems   isacs 14571

### PART 8  BASIC CATEGORY THEORY

#### 8.1  Categories

##### 8.1.1  Categories   ccat 14584

##### 8.1.2  Opposite category   coppc 14632

##### 8.1.3  Monomorphisms and epimorphisms   cmon 14649

##### 8.1.4  Sections, inverses, isomorphisms   csect 14665

##### 8.1.5  Subcategories   cssc 14702

##### 8.1.6  Functors   cfunc 14746

##### 8.1.7  Full & faithful functors   cful 14794

##### 8.1.8  Natural transformations and the functor category   cnat 14833

#### 8.2  Arrows (disjointified hom-sets)

##### 8.2.1  Identity and composition for arrows   cida 14903

#### 8.3  Examples of categories

##### 8.3.1  The category of sets   csetc 14925

##### 8.3.2  The category of categories   ccatc 14944

#### 8.4  Categorical constructions

##### 8.4.1  Product of categories   cxpc 14960

##### 8.4.2  Functor evaluation   cevlf 15001

##### 8.4.3  Hom functor   chof 15040

### PART 9  BASIC ORDER THEORY

#### 9.1  Presets and directed sets using extensible structures

#### 9.2  Posets and lattices using extensible structures

##### 9.2.1  Posets   cpo 15092

##### 9.2.2  Lattices   clat 15197

##### 9.2.3  The dual of an ordered set   codu 15280

##### 9.2.4  Subset order structures   cipo 15303

##### 9.2.5  Distributive lattices   latmass 15340

##### 9.2.6  Posets and lattices as relations   cps 15350

##### 9.2.7  Directed sets, nets   cdir 15380

### PART 10  BASIC ALGEBRAIC STRUCTURES

#### 10.1  Monoids

##### 10.1.1  Definition and basic properties   cmnd 15391

##### 10.1.2  Monoid homomorphisms and submonoids   cmhm 15444

##### 10.1.3  Ordered group sum operation   gsumvallem1 15481

##### 10.1.4  Free monoids   cfrmd 15504

#### 10.2  Groups

##### 10.2.1  Definition and basic properties   df-grp 15524

##### 10.2.2  Subgroups and Quotient groups   csubg 15654

##### 10.2.3  Elementary theory of group homomorphisms   cghm 15723

##### 10.2.4  Isomorphisms of groups   cgim 15764

##### 10.2.5  Group actions   cga 15786

##### 10.2.6  Centralizers and centers   ccntz 15812

##### 10.2.7  The opposite group   coppg 15839

##### 10.2.8  Symmetric groups   csymg 15861

###### 10.2.8.1  Definition and basic properties   csymg 15861

###### 10.2.8.2  Cayley's theorem   cayleylem1 15896

###### 10.2.8.3  Permutations fixing one element   symgfix2 15900

###### 10.2.8.4  Transpositions in the symmetric group   cpmtr 15926

###### 10.2.8.5  The sign of a permutation   cpsgn 15974

##### 10.2.9  p-Groups and Sylow groups; Sylow's theorems   cod 16007

##### 10.2.10  Direct products   clsm 16112

##### 10.2.11  Free groups   cefg 16182

#### 10.3  Abelian groups

##### 10.3.1  Definition and basic properties   ccmn 16256

##### 10.3.2  Cyclic groups   ccyg 16333

##### 10.3.3  Group sum operation   gsumval3a 16358

##### 10.3.4  Internal direct products   cdprd 16448

##### 10.3.5  The Fundamental Theorem of Abelian Groups   ablfacrplem 16539

#### 10.4  Rings

##### 10.4.1  Multiplicative Group   cmgp 16564

##### 10.4.2  Definition and basic properties   crg 16576

##### 10.4.3  Opposite ring   coppr 16647

##### 10.4.4  Divisibility   cdsr 16663

##### 10.4.5  Ring homomorphisms   crh 16737

#### 10.5  Division rings and fields

##### 10.5.1  Definition and basic properties   cdr 16755

##### 10.5.2  Subrings of a ring   csubrg 16784

##### 10.5.3  Absolute value (abstract algebra)   cabv 16824

##### 10.5.4  Star rings   cstf 16851

#### 10.6  Left modules

##### 10.6.1  Definition and basic properties   clmod 16871

##### 10.6.2  Subspaces and spans in a left module   clss 16934

##### 10.6.3  Homomorphisms and isomorphisms of left modules   clmhm 17021

##### 10.6.4  Subspace sum; bases for a left module   clbs 17076

#### 10.7  Vector spaces

##### 10.7.1  Definition and basic properties   clvec 17104

#### 10.8  Ideals

##### 10.8.1  The subring algebra; ideals   csra 17170

##### 10.8.2  Two-sided ideals and quotient rings   c2idl 17234

##### 10.8.3  Principal ideal rings. Divisibility in the integers   clpidl 17244

##### 10.8.4  Nonzero rings   cnzr 17260

##### 10.8.5  Left regular elements. More kinds of rings   crlreg 17271

#### 10.9  Associative algebras

##### 10.9.1  Definition and basic properties   casa 17302

#### 10.10  Abstract multivariate polynomials

##### 10.10.1  Definition and basic properties   cmps 17339

##### 10.10.2  Polynomial evaluation   evlslem4OLD 17517

##### 10.10.3  Univariate polynomials   cps1 17525

#### 10.11  The complex numbers as an algebraic extensible structure

##### 10.11.1  Definition and basic properties   cpsmet 17643

##### 10.11.2  Ring of integers   zring 17724

##### 10.11.3  Algebraic constructions based on the complex numbers   czrh 17772

##### 10.11.4  Signs as subgroup of the complex numbers   cnmsgnsubg 17848

##### 10.11.5  Embedding of permutation signs into a ring   zrhpsgnmhm 17855

##### 10.11.6  The ordered field of real numbers   crefld 17875

#### 10.12  Generalized pre-Hilbert and Hilbert spaces

##### 10.12.1  Definition and basic properties   cphl 17894

##### 10.12.2  Orthocomplements and closed subspaces   cocv 17926

##### 10.12.3  Orthogonal projection and orthonormal bases   cpj 17966

### PART 11  BASIC LINEAR ALGEBRA

#### 11.1  Vectors and free modules

##### 11.1.1  Direct sum of left modules   cdsmm 17997

##### 11.1.2  Free modules   cfrlm 18012

##### 11.1.3  Standard basis (unit vectors)   cuvc 18048

##### 11.1.4  Independent sets and families   clindf 18074

##### 11.1.5  Characterization of free modules   lmimlbs 18106

#### 11.2  Matrices

##### 11.2.1  The matrix algebra   cmmul 18120

##### 11.2.2  Multiplication of a matrix with a "column vector"   cmvmul 18192

##### 11.2.3  Replacement functions for a square matrix   cmarrep 18208

##### 11.2.4  Submatrices   csubma 18228

#### 11.3  The determinant

##### 11.3.1  Definition and basic properties   cmdat 18236

##### 11.3.2  Determinants of 2 x 2 -matrices   m2detleiblem1 18271

##### 11.3.3  The matrix adjugate/adjunct   cmadu 18279

##### 11.3.4  Laplace expansion of determinants (special case)   symgmatr01lem 18300

##### 11.3.5  Inverse matrix   invrvald 18323

##### 11.3.6  Cramer's rule   slesolvec 18326

### PART 12  BASIC TOPOLOGY

#### 12.1  Topology

##### 12.1.1  Topological spaces   ctop 18339

##### 12.1.2  TopBases for topologies   isbasisg 18393

##### 12.1.3  Examples of topologies   distop 18441

##### 12.1.4  Closure and interior   ccld 18461

##### 12.1.5  Neighborhoods   cnei 18542

##### 12.1.6  Limit points and perfect sets   clp 18579

##### 12.1.7  Subspace topologies   restrcl 18602

##### 12.1.8  Order topology   ordtbaslem 18633

##### 12.1.9  Limits and continuity in topological spaces   ccn 18669

##### 12.1.10  Separated spaces: T0, T1, T2 (Hausdorff) ...   ct0 18751

##### 12.1.11  Compactness   ccmp 18830

##### 12.1.12  Bolzano-Weierstrass theorem   bwth 18854

##### 12.1.13  Connectedness   ccon 18856

##### 12.1.14  First- and second-countability   c1stc 18882

##### 12.1.15  Local topological properties   clly 18909

##### 12.1.16  Compactly generated spaces   ckgen 18947

##### 12.1.17  Product topologies   ctx 18974

##### 12.1.18  Continuous function-builders   cnmptid 19075

##### 12.1.19  Quotient maps and quotient topology   ckq 19107

##### 12.1.20  Homeomorphisms   chmeo 19167

#### 12.2  Filters and filter bases

##### 12.2.1  Filter bases   elmptrab 19241

##### 12.2.2  Filters   cfil 19259

##### 12.2.3  Ultrafilters   cufil 19313

##### 12.2.4  Filter limits   cfm 19347

##### 12.2.5  Extension by continuity   ccnext 19472

##### 12.2.6  Topological groups   ctmd 19482

##### 12.2.7  Infinite group sum on topological groups   ctsu 19537

##### 12.2.8  Topological rings, fields, vector spaces   ctrg 19571

#### 12.3  Uniform Structures and Spaces

##### 12.3.1  Uniform structures   cust 19615

##### 12.3.2  The topology induced by an uniform structure   cutop 19646

##### 12.3.3  Uniform Spaces   cuss 19669

##### 12.3.4  Uniform continuity   cucn 19691

##### 12.3.5  Cauchy filters in uniform spaces   ccfilu 19702

##### 12.3.6  Complete uniform spaces   ccusp 19713

#### 12.4  Metric spaces

##### 12.4.1  Pseudometric spaces   ispsmet 19721

##### 12.4.2  Basic metric space properties   cxme 19733

##### 12.4.3  Metric space balls   blfvalps 19799

##### 12.4.4  Open sets of a metric space   mopnval 19854

##### 12.4.5  Continuity in metric spaces   metcnp3 19956

##### 12.4.6  The uniform structure generated by a metric   metuvalOLD 19965

##### 12.4.7  Examples of metric spaces   dscmet 20006

##### 12.4.8  Normed algebraic structures   cnm 20010

##### 12.4.9  Normed space homomorphisms (bounded linear operators)   cnmo 20125

##### 12.4.10  Topology on the reals   qtopbaslem 20178

##### 12.4.11  Topological definitions using the reals   cii 20292

##### 12.4.12  Path homotopy   chtpy 20380

##### 12.4.13  The fundamental group   cpco 20413

#### 12.5  Complex metric vector spaces

##### 12.5.1  Complex left modules   cclm 20475

##### 12.5.2  Complex vector spaces   ccvs 20517

##### 12.5.3  Complex pre-Hilbert space   ccph 20526

##### 12.5.4  Convergence and completeness   ccfil 20604

##### 12.5.5  Baire's Category Theorem   bcthlem1 20676

##### 12.5.6  Banach spaces and complex Hilbert spaces   ccms 20684

###### 12.5.6.1  The complete ordered field of the real numbers   retopn 20724

##### 12.5.7  Euclidean spaces   crrx 20728

##### 12.5.8  Minimizing Vector Theorem   minveclem1 20752

##### 12.5.9  Projection Theorem   pjthlem1 20765

### PART 13  BASIC REAL AND COMPLEX ANALYSIS

#### 13.1  Continuity

##### 13.1.1  Intermediate value theorem   pmltpclem1 20773

#### 13.2  Integrals

##### 13.2.1  Lebesgue measure   covol 20787

##### 13.2.2  Lebesgue integration   cmbf 20935

###### 13.2.2.1  Lesbesgue integral   cmbf 20935

###### 13.2.2.2  Lesbesgue directed integral   cdit 21162

#### 13.3  Derivatives

##### 13.3.1  Real and complex differentiation   climc 21178

###### 13.3.1.1  Derivatives of functions of one complex or real variable   climc 21178

###### 13.3.1.2  Results on real differentiation   dvferm1lem 21297

### PART 14  BASIC REAL AND COMPLEX FUNCTIONS

#### 14.1  Polynomials

##### 14.1.1  Abstract polynomials, continued   evlslem6 21363

##### 14.1.2  Polynomial degrees   cmdg 21406

##### 14.1.3  The division algorithm for univariate polynomials   cmn1 21481

##### 14.1.4  Elementary properties of complex polynomials   cply 21536

##### 14.1.5  The division algorithm for polynomials   cquot 21640

##### 14.1.6  Algebraic numbers   caa 21664

##### 14.1.7  Liouville's approximation theorem   aalioulem1 21682

#### 14.2  Sequences and series

##### 14.2.1  Taylor polynomials and Taylor's theorem   ctayl 21702

##### 14.2.2  Uniform convergence   culm 21725

##### 14.2.3  Power series   pserval 21759

#### 14.3  Basic trigonometry

##### 14.3.1  The exponential, sine, and cosine functions (cont.)   efcn 21792

##### 14.3.2  Properties of pi = 3.14159...   pilem1 21800

##### 14.3.3  Mapping of the exponential function   efgh 21881

##### 14.3.4  The natural logarithm on complex numbers   clog 21890

##### 14.3.5  Theorems of Pythagoras, isosceles triangles, and intersecting chords   angval 22081

##### 14.3.6  Solutions of quadratic, cubic, and quartic equations   quad2 22118

##### 14.3.7  Inverse trigonometric functions   casin 22141

##### 14.3.8  The Birthday Problem   log2ublem1 22225

##### 14.3.9  Areas in R^2   carea 22233

##### 14.3.10  More miscellaneous converging sequences   rlimcnp 22243

##### 14.3.11  Inequality of arithmetic and geometric means   cvxcl 22262

##### 14.3.12  Euler-Mascheroni constant   cem 22269

#### 14.4  Basic number theory

##### 14.4.1  Wilson's theorem   wilthlem1 22290

##### 14.4.2  The Fundamental Theorem of Algebra   ftalem1 22294

##### 14.4.3  The Basel problem (ζ(2) = π2/6)   basellem1 22302

##### 14.4.4  Number-theoretical functions   ccht 22312

##### 14.4.5  Perfect Number Theorem   mersenne 22450

##### 14.4.6  Characters of Z/nZ   cdchr 22455

##### 14.4.7  Bertrand's postulate   bcctr 22498

##### 14.4.8  Legendre symbol   clgs 22517

##### 14.4.9  Quadratic reciprocity   lgseisenlem1 22572

##### 14.4.10  All primes 4n+1 are the sum of two squares   2sqlem1 22586

##### 14.4.11  Chebyshev's Weak Prime Number Theorem, Dirichlet's Theorem   chebbnd1lem1 22602

##### 14.4.12  The Prime Number Theorem   mudivsum 22663

##### 14.4.13  Ostrowski's theorem   abvcxp 22748

### PART 15  ELEMENTARY GEOMETRY

#### 15.1  Definition and Tarski's Axioms of Geometry

#### 15.2  Tarskian Geometry

##### 15.2.1  Congruence   tgcgrcomlr 22818

##### 15.2.2  Betweenness   tgbtwntriv2 22822

##### 15.2.3  Dimension   tglowdim1 22834

##### 15.2.4  Betweenness and Congruence   tgifscgr 22841

##### 15.2.5  Congruence of a series of points   ccgrg 22843

##### 15.2.6  Colinearity   tglng 22860

##### 15.2.7  Connectivity of betweenness   tgbtwnconn1lem1 22879

##### 15.2.8  Less-than relation in geometric congruences   cleg 22888

##### 15.2.9  Lines and rays   btwnlng1 22899

##### 15.2.10  Midpoints and point inversions   cmid 22919

#### 15.3  Properties of geometries

##### 15.3.1  Isomorphisms between geometries   f1otrgds 22937

#### 15.4  Geometry in Hilbert spaces

##### 15.4.1  Geometry in the complex plane   cchhllem 22955

##### 15.4.2  Geometry in Euclidean spaces   cee 22956

###### 15.4.2.1  Definition of the Euclidean space   cee 22956

###### 15.4.2.2  Tarski's axioms for geometry for the Euclidean space   axdimuniq 22981

###### 15.4.2.3  EE^n fulfills Tarski's Axioms   ceeng 23045

### PART 16  GRAPH THEORY

#### 16.1  Undirected graphs - basics

##### 16.1.1  Undirected hypergraphs   cuhg 23055

##### 16.1.2  Undirected multigraphs   cumg 23068

##### 16.1.3  Undirected simple graphs   cuslg 23085

###### 16.1.3.1  Undirected simple graphs - basics   cuslg 23085

###### 16.1.3.2  Undirected simple graphs - examples   usgraexvlem 23135

###### 16.1.3.3  Finite undirected simple graphs   fiusgraedgfi 23142

##### 16.1.4  Neighbors, complete graphs and universal vertices   cnbgra 23151

###### 16.1.4.1  Neighbors   nbgraop 23157

###### 16.1.4.2  Complete graphs   iscusgra 23186

###### 16.1.4.3  Universal vertices   isuvtx 23218

##### 16.1.5  Walks, paths and cycles   cwalk 23227

###### 16.1.5.1  Walks and trails   wlks 23247

###### 16.1.5.2  Paths and simple paths   pths 23287

###### 16.1.5.3  Circuits and cycles   crcts 23330

###### 16.1.5.4  Connected graphs   cconngra 23377

##### 16.1.6  Vertex Degree   cvdg 23385

#### 16.2  Eulerian paths and the Konigsberg Bridge problem

##### 16.2.1  Eulerian paths   ceup 23405

##### 16.2.2  The Konigsberg Bridge problem   vdeg0i 23425

### PART 17  GUIDES AND MISCELLANEA

#### 17.1  Guides (conventions, explanations, and examples)

##### 17.1.1  Conventions   conventions 23431

##### 17.1.2  Natural deduction   natded 23432

##### 17.1.3  Natural deduction examples   ex-natded5.2 23433

##### 17.1.4  Definitional examples   ex-or 23450

#### 17.2  Humor

##### 17.2.1  April Fool's theorem   avril1 23478

#### 17.3  (Future - to be reviewed and classified)

##### 17.3.1  Planar incidence geometry   cplig 23484

##### 17.3.2  Algebra preliminaries   crpm 23489

##### 17.3.3  Transitive closure   ctcl 23491


