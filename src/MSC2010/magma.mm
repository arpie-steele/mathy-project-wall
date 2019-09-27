$[ set.mm $]

$(
  Add to #bib section of mmset.raw.html :

  <LI><A NAME="Bruck"></A> [Bruck] Richard Hubert Bruck, <I>A Survey
  of Binary Systems</I>, 3rd Edition, Springer-Verlag Berlin,
  Heidelberg (1971);</LI>

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                   Single-Valued Mappings and Partial Binary Operations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c PartialBinOp $.

  ${
    $( Placeholder lemma. $)
    fveu2lem $p |- ( A Fn G -> ( ran A C_ H -> ( g e. G -> ( x = ( A ` g ) -> ( ( h e. H /\ ( A ` g ) = h ) <-> h = x ) ) ) ) ) $= ? $.

  $}

  ${
    $d g h x A $.  $d g h x G $.  $d g h x H $.

    $( A single-valued mapping ` A ` of a set ` G ` into a set ` H ` is a
       correspondence which assigns to each ` g ` in ` G ` a unique element
       ` ( A `` g ) ` in ` H ` .

       [Bruck] p. 1 $)
    fveu2 $p |- ( A : G --> H -> A. g e. G E! h e. H ( A ` g ) = h ) $=
      cG cH cA wf vg cv cA cfv vh cv wceq vh cH wreu vg cG cG cH cA wf cA cG
      wfn cA crn cH wss wa vg cv cG wcel vg cv cA cfv vh cv wceq vh cH wreu wi
      cG cH cA df-f cA cG wfn cA crn cH wss vg cv cG wcel vg cv cA cfv vh cv
      wceq vh cH wreu wi cA cG wfn cA crn cH wss vg cv cG wcel vg cv cA cfv vh
      cv wceq vh cH wreu cA cG wfn cA crn cH wss vg cv cG wcel w3a vh cv cH
      wcel vg cv cA cfv vh cv wceq wa vh weu vg cv cA cfv vh cv wceq vh cH wreu
      cA cG wfn cA crn cH wss vg cv cG wcel w3a vh cv cH wcel vg cv cA cfv vh
      cv wceq wa vh vx weq wb vh wal vx wex vh cv cH wcel vg cv cA cfv vh cv
      wceq wa vh weu cA cG wfn cA crn cH wss vg cv cG wcel w3a vh cv cH wcel vg
      cv cA cfv vh cv wceq wa vh vx weq wb vh wal vx ? cA cG wfn cA crn cH wss
      vg cv cG wcel w3a cA cG wfn cA crn cH wss vg cv cG wcel w3a vx cA cG wfn
      cA crn cH wss vg cv cG wcel w3a id alrimiv vx cv vg cv cA cfv wceq cA cG
      wfn cA crn cH wss vg cv cG wcel w3a vh cv cH wcel vg cv cA cfv vh cv wceq
      wa vh vx weq wb vh vx cv vg cv cA cfv wceq vh ax-5 cA cG wfn cA crn cH
      wss vg cv cG wcel w3a vh ax-5 cA cG wfn cA crn cH wss vg cv cG wcel w3a
      vx cv vg cv cA cfv wceq vh cv cH wcel vg cv cA cfv vh cv wceq wa vh vx
      weq wb cA cG wfn cA crn cH wss vg cv cG wcel vx cv vg cv cA cfv wceq vh
      cv cH wcel vg cv cA cfv vh cv wceq wa vh vx weq wb wi ? 3imp com12
      alrimdh spimeh vh cv cH wcel vg cv cA cfv vh cv wceq wa vh vx df-eu
      sylibr vg cv cA cfv vh cv wceq vh cH df-reu sylibr 3exp imp sylbi
      ralrimiv $.

$(
Stuck at 
|- ( A Fn G -> ( ran A C_ H -> ( g
   e. G -> ( x = ( A ` g ) -> ( ( h e. H /\ ( A ` g ) = h ) <-> h = x ) ) ) ) )

$)

  $}

  ${
    $d g A $.  $d g B $.  $d g G $.  $d g H $.

    $( If ` A , B ` are single-valued mappings of ` G ` into ` H ` then
       ` A = B ` if and only if ` ( A `` g ) = ( B `` g ) ` for every ` g ` in
       ` G ` .  See ~ eqfnfv .

       [Bruck] p. 1 
       (Contributed by Richard Penner, 26-Sep-2019.) $)
    eqffv $p |- ( ( A : G --> H /\ B : G --> H ) -> ( A = B <->
              A. g e. G ( A ` g ) = ( B ` g ) ) ) $=
      cG cH cA wf cG cH cB wf wa cA cG wfn cB cG wfn wa cA cB wceq vg cv cA cfv
      vg cv cB cfv wceq vg cG wral wb cG cH cA wf cA cG wfn cG cH cB wf cB cG
      wfn cG cH cA ffn cG cH cB ffn anim12i vg cG cA cB eqfnfv syl $.
  $}

  ${
    $( We allow the possibility that ` G ` may be the empty set.

       [Bruck] p. 1

       (Contributed by Richard Penner, 26-Sep-2019.) $)
    0fex $p |- ( ( A : G --> H /\ G = (/) ) -> A e. _V ) $=
    cG c0 wceq cG cH cA wf cG cvv wcel cA cvv wcel c0 cvv wcel cG c0 wceq cG
    cvv wcel wi 0ex c0 cvv cG eleq1a ax-mp cG cH cvv cA fex sylan2 $.
  $}

  ${
  $( If ` G , H ` are non-empty sets, the logical product
     ` G X. H ` is the set of all ordered pairs ` <. a , b >. ` ,
     ` a ` in ` G ` , ` b ` in ` H ` , where
     ` <. a , b >. = <. c , d >. ` if and only if ` a = c ` , ` b = d ` .
     See ~ df-xp and ~ opthg .

     [Bruck] p. 1
  $)
  $}

  ${
    $d x y u v $.
    $( By a (single-valued) _binary operation_ ` A ` on the (non-empty) set G
       we mean a single-valued mapping ` A ` from some subset ` dom A ` of
       ` G X. G ` into G. Here ` dom A ` is the is the _domain_ of ` A ` ;

       *N. B.* Bruck uses _range_ for what metamath calls ` dom ` .

       Definition binary operation in [Bruck] p. 1 $)
    df-pbo $a |- PartialBinOp = { <. x , y >. | ( y =/= (/) /\ x C_ ( ( y X. y ) X. y ) /\ A. u E* v u x v ) } $.
  $}

  ${
    $( we allow the possibility that ` dom A ` may be empty.

       [Bruck] p. 1 $)
    pbodm0 $p |- ( A = (/) -> A. b ( b =/= (/) -> ( A PartialBinOp b /\ dom A = (/) ) ) ) $= ? $.
  $}

  ${
    $( Two binary operations ` A , B ` on G are equal ( ` A = B ` ) if and only
       if ` dom A = dom B ` and ` A = B ` on ` dom A ` .

       [Bruck] p. 1 $)
    eqpbo $p |- ( ( A PartialBinOp G /\ B PartialBinOp G ) -> ( A = B <-> ( dom A = dom B /\ A. x e. dom A ( A ` x ) = ( B ` x ) ) ) ) $= ? $.
  $}

$( We make the following conventions in connection with a binary operation ` A ` on ` G ` :

   [Bruck] p. 1
$)

  ${
    $( (1) If ` <. a , b >. ` is in ` dom A ` , we usually write the "product"
       ` ( a A b ) ` instead of ` ( A `` <. a , b >. ) ` .  See ~ df-ov .

       [Bruck] p. 1 $)
    pbov $p |- ( ( A PartialBinOp B /\ <. a , b >. e. dom A ) -> ( a A b ) = ( A ` <. a , b >. ) ) $= ? $.

  $}

$( (2) The statement " ` ( a A b ) ` is defined in ` G ` " means that
   ` <. a , b >. ` is in ` dom A ` .

   (3) The statement " ` a b = c ` in ` G ` " means ` <. a , b >. `
   is in ` dom A ` , ` c ` is in ` G ` and
   ` ( A `` <. a , b >. ) = c ` . It will be obvious from the
   context what operations are in question.

   [Bruck] p. 1
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                   Partial Magmas
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  A partial magma is a universal algebra with one (perhaps
  incompletely-defined) binary operation, which need not have any
  special conditions placed on it (other than the closure property
  common to binary operations).

  In [Bruck] and earlier works, these are called _halfgroupoids_
  which is not quantitatively correct and inconvinient in that
  groupoid is more commonly associated today with a entirely different
  concept in the theory of categories.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c PartialMagma $.
  $c SubPartialMagma $.

  $( Extend class notation with the class of all magmas. $)
  cpmgm $a class PartialMagma $.
  $( Define subset of Partial Magma $)
  cspmgm $a class SubPartialMagma $.

  ${

    $d b g x y $.
    $( Definition of a partial magma.  A partial magma is a non-empty set
       equipped with perhaps only partially-defined internal operation ( see
       ~ pmgmcl ).

       Based on definition halfgroupoid in [Bruck] p. 1. $)
    df-pmgm $a |- PartialMagma = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ]. ( b =/= (/) /\ A. x e. b A. y e. b ( <. x , y >. e. dom p -> ( x p y ) e. b ) ) } $.

  $}

  ${
    ispmgm.b $e |- B = ( Base ` G ) $.
    ispmgm.p $e |- .+ = ( +g ` G ) $.
    $( The predicate "is a partial magma." $)
    ispmgm $p |- ( G e. PartialMagma <-> ( B =/= (/) /\ A. a e. B A. b e. B ( <. a , b >. e. dom .+ /\ ( a .+ b ) e. B ) ) ) $= ? $.

  $}

  ${
    ispmgm2.b $e |- B = ( Base ` G ) $.
    ispmgm2.p $e |- .+ = ( +g ` G ) |` ( B X. B ) $.
    ispmgm2.s $e |- S = dom .+ $.
    $( The predicate "is a partial magma." $)
    ispmgm2 $p |- ( G e. PartialMagma <-> ( B =/= (/) /\ .+ : S --> B ) ) $= ? $.

  $}

  ${
    ispmgm3.b $e |- B = ( Base ` G ) $.
    ispmgm3.p $e |- .+ = ( +g ` G ) |` ( B X. B ) $.
    $( A _halfgroupoid_ ` G ` is a system consisting of a non-empty set ` G `
       and a binary operation on ` G ` .

       Based on definition halfgroupoid in [Bruck] p. 1. $)
    ispmgm3 $p |- ( G e. PartialMagma <-> .+ PartialBinOp B ) $= ? $.

  $}

$( A (proper or improper) subset ` H ` of the halfgroupoid ` G `
   is a _subhalfgroupoid_ ` G ` such that ` a b = c ` in ` G `
   whenever ` a b = c ` in ` H ` .

   Definition subhalfgroupoid in [Bruck] p. 1.
$)

  ${

    $d b c g h $.
    $( Definition of a sub partial magma.  A sub partial magma is partial magma
       where the operation (restricted to the base set) is a subset of that of
       another partial magma.

       Based on definition subhalfgroupoid in [Bruck] p. 1. $)
    df-spmgm $a |- SubPartialMagma = { <. h , g >. | ( h e. PartialMagma /\ g e. PartialMagma /\ [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ]. [. ( Base ` h ) / c ]. [. ( +g ` h ) / o ]. ( o |` ( c X. c ) ) C_ ( p |` ( b X. b ) ) ) } $.

  $}


  ${
    isspmgm.c $e |- S = ( Base ` H ) $.
    isspmgm.b $e |- B = ( Base ` G ) $.
    isspmgm.o $e |- .(+) = ( +g ` H ) $.
    isspmgm.p $e |- .+ = ( +g ` G ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    isspmgm $p ( H SubPartialMagma G <-> ( H e. PartialMagma /\ G e. PartialMagma /\ ( .(+) |` ( H X. H ) ) C_ ( .+ |` ( B X. B ) ) ) ) $= ? $.
  $}

  ${
    isspmgm2.c $e |- S = ( Base ` H ) $.
    isspmgm2.b $e |- B = ( Base ` G ) $.
    isspmgm2.o $e |- .(+) = ( +g ` H ) |` ( S X. S ) $.
    isspmgm2.p $e |- .+ = ( +g ` G ) |` ( B X. B ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    isspmgm2 $p ( H SubPartialMagma G <-> ( H e. PartialMagma /\ G e. PartialMagma /\ .(+) C_ .+ ) ) $= ? $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                   Magmas
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  A magma is a universal algebra with one binary operation, which
  need not have any special conditions placed on it (other than the
  closure property common to binary operations).
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c MagmaNEW $.
  $c MagmaRP $.
  $c SubMagma $.

  $( Extend class notation with the class of all magmas. $)
  cmgmNEW $a class MagmaNEW $.
  $( Extend class notation with the class of all magmas. $)
  cmgm $a class MagmaRP $.
  $( PLEASE PUT DESCRIPTION HERE. $)
  csmgm $a class SubMagma $.

$( df-gsum can be used to map words to elements of a magma. See gsumval2a $)

$( mndcl proves a Mnd is closed under the binary operation, thus a magma. $)

  ${

    $d b g x y $.
    $( Definition of a magma.  A magma is a non-empty set equipped with a
       completely-defined internal operation ( see ~ mgmcl ).

       Based on definition groupoid in [Bruck] p. 1. $)
    df-mgmRP $a |- MagmaRP = { g e. PartialMagma | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ]. A. x e. b A. y e. b ( <. x , y >. e. dom b /\ ( x p y ) e. b ) } $.

  $}

  ${

    $d b g x y $.
    $( Definition of a magma.  A magma is a set equipped with an everywhere
       defined internal operation ( see ~ mgmclNEW ). $)
    df-mgmNEW $a |- MagmaNEW = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ].
A. x e. b A. y e. b ( x p y ) e. b } $.
  $}

  ${
    $d u v y $.  $d u v x A $.  $d u v x B $.  $d u v x C $.  $d u v x F $.
    $( This lemma might be useful. $)
    dfmgm2lem1 $p |- ( A. x e. ( A X. B ) E! y e. C x F y <-> A. u e. A A. v e. B ( u F v ) e. C ) $=
        vx cv vy cv cF wbr vy cC wreu vu cv vv cv cF co cC wcel vx vu vv cA cB
        ? ralxp $.
  $}

  ${
    $( PLEASE PUT DESCRIPTION HERE. $)
    dfmgm2 $p |- MagmaNEW = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ].
( p |` ( b X. b ) ) : ( b X. b ) --> b } $= ? $.
  $}

  ${
    ismgmRP.b $e |- B = ( Base ` G ) $.
    ismgmRP.p $e |- .+ = ( +g ` G ) $.
    $( The predicate "is a magma." $)
    ismgmRP $p |- ( G e. MagmaRP <-> ( B =/= (/) /\ A. a e. B A. b e. B ( <. a , b >. e. dom .+ /\ ( a .+ b ) e. B ) ) ) $= ? $.

  $}

  ${
    ismgm2.b $e |- B = ( Base ` G ) $.
    ismgm2.p $e |- .+ = ( +g ` G ) |` ( B X. B ) $.
    $( The predicate "is a magma." $)
    ismgm2 $p |- ( G e. MagmaRP <-> ( B =/= (/) /\ .+ : ( B X. B ) --> B ) ) $= ? $.
  $}

  ${
    ismgm3.b $e |- B = ( Base ` G ) $.
    ismgm3.p $e |- .+ = ( +g ` G ) $.
    $( A _groupoid_ ` G ` is a halfgroupoid such that ` a b ` is defined in
       ` G ` for all ` a , b ` in ` G ` .

       Based on definition halfgroupoid in [Bruck] p. 1. $)
    ismgm3 $p |- ( G e. MagmaRP <-> ( G e. PartialMagma /\ ( B X. B ) C_ dom .+ ) ) $= ? $.

  $}

  ${
    ismgm4.b $e |- B = ( Base ` G ) $.
    ismgm4.p $e |- .+ = ( +g ` G ) $.
    $( A _groupoid_ ` G ` is a halfgroupoid such that ` a b ` is defined in
       ` G ` for all ` a , b ` in ` G ` .

       Based on definition halfgroupoid in [Bruck] p. 1. $)
    ismgm4 $p |- ( G e. MagmaRP <-> ( G e. PartialMagma /\ A. a e. B A. b e. B <. a , b >. e. dom .+ ) ) $= ? $.

  $}

  ${

    $d a b g v p B $.  $d a b g v p G $.  $d a b g v p .+ $.
    ismgmNEW.g $e |- G e. _V $.
    ismgmNEW.b $e |- B = ( Base ` G ) $.
    ismgmNEW.p $e |- .+ = ( +g ` G ) $.
    $( The predicate "is a magma."  (Contributed by Richard Penner,
       21-Sep-2019.) $)
    ismgmNEW $p |- ( G e. MagmaNEW <-> A. a e. B A. b e. B ( a .+ b ) e. B ) $=
      cG cmgmNEW wcel cG va cv vb cv vp cv co vv cv wcel vb vv cv wral va vv cv
      wral vp vg cv cplusg cfv wsbc vv vg cv cbs cfv wsbc vg cab wcel va cv vb
      cv c.pl co cB wcel vb cB wral va cB wral cmgmNEW va cv vb cv vp cv co vv
      cv wcel vb vv cv wral va vv cv wral vp vg cv cplusg cfv wsbc vv vg cv cbs
      cfv wsbc vg cab cG va vb vg vp vv df-mgmNEW eleq2i va cv vb cv vp cv co
      vv cv wcel vb vv cv wral va vv cv wral vp vg cv cplusg cfv wsbc vv vg cv
      cbs cfv wsbc va cv vb cv c.pl co cB wcel vb cB wral va cB wral vg cG cG
      cvv wcel va cv vb cv c.pl co cB wcel vb cB wral va cB wral cG cvv
      ismgmNEW.g elexi a1i vg cv cG wceq va cv vb cv vp cv co vv cv wcel vb vv
      cv wral va vv cv wral vp vg cv cplusg cfv wsbc va cv vb cv c.pl co cB
      wcel vb cB wral va cB wral vv vg cv cbs cfv cB cvv vg cv cbs cfv cvv wcel
      vg cv cG wceq vg cv cbs fvex a1i vg cv cG wceq vg cv cbs cfv cG cbs cfv
      cB vg cv cG cbs fveq2 ismgmNEW.b syl6eqr vg cv cG wceq vv cv cB wceq wa
      va cv vb cv vp cv co vv cv wcel vb vv cv wral va vv cv wral va cv vb cv
      c.pl co cB wcel vb cB wral va cB wral vp vg cv cplusg cfv c.pl cvv vg cv
      cplusg cfv cvv wcel vg cv cG wceq vv cv cB wceq wa vg cv cplusg fvex a1i
      vg cv cG wceq vv cv cB wceq wa vg cv cplusg cfv cG cplusg cfv c.pl vg cv
      cG wceq vv cv cB wceq wa vg cv cG cplusg vg cv cG wceq vv cv cB wceq
      simpl fveq2d ismgmNEW.p syl6eqr vg cv cG wceq vv cv cB wceq wa vp cv c.pl
      wceq wa va cv vb cv vp cv co vv cv wcel vb vv cv wral va cv vb cv c.pl co
      cB wcel vb cB wral va vv cv cB vg cv cG wceq vv cv cB wceq vp cv c.pl
      wceq simplr vg cv cG wceq vv cv cB wceq wa vp cv c.pl wceq wa va cv vb cv
      vp cv co vv cv wcel va cv vb cv c.pl co cB wcel vb vv cv cB vg cv cG wceq
      vv cv cB wceq vp cv c.pl wceq simplr vg cv cG wceq vv cv cB wceq wa vp cv
      c.pl wceq wa va cv vb cv vp cv co va cv vb cv c.pl co vv cv cB vg cv cG
      wceq vv cv cB wceq wa vp cv c.pl wceq wa vp cv c.pl va cv vb cv vg cv cG
      wceq vv cv cB wceq wa vp cv c.pl wceq simpr oveqd vg cv cG wceq vv cv cB
      wceq vp cv c.pl wceq simplr eleq12d raleqbidv raleqbidv sbcied2 sbcied2
      elab3 bitri $.

  $}

  ${
    $d u w x B $.  $d u w x .+ $.
    $( A two-sided identity element is unique (if it exists) in any magma.
       (Contributed by Mario Carneiro, 7-Dec-2014.)  (Revised by NM,
       17-Jun-2017.) $)
    mgmidmoMOVE $p |- E* u e. B A. x e. B ( ( u .+ x ) = x /\ ( x .+ u ) = x ) $=
      ( vw cv co wceq wa wral wrmo weq wcel ralimi oveq1 id rspcva oveq2 eqeq1d
      eqeq12d wi simpl simpr sylan9req an42s syl2ani anbi12d ralbidv rmo4 mpbir
      ex rgen2a ) BFZAFZDGZUNHZUNUMDGZUNHZIZACJZBCKUTEFZUNDGZUNHZUNVADGZUNHZIZA
      CJZIBELZUAZECJBCJVIBECUTUMCMZVACMZIZUPACJZVEACJZVHVGUSUPACUPURUBNVFVEACVC
      VEUCNVLVMVNIVHVJVNVKVMVHVJVNIVKVMIUMUMVADGZVAVEVOUMHAUMCABLZVDVOUNUMUNUMV
      ADOVPPTQUPVOVAHAVACAELZUOVOUNVAUNVAUMDRVQPTQUDUEUKUFULUTVGBECVHUSVFACVHUP
      VCURVEVHUOVBUNUMVAUNDOSVHUQVDUNUMVAUNDRSUGUHUIUJ $.

  $}


  ${
    $d a b B $.  $d a b G $.  $d a b .+ $.  $d a b X $.  $d b Y $.
    mgmclNEW.g $e |- G e. _V $.
    mgmclNEW.b $e |- B = ( Base ` G ) $.
    mgmclNEW.p $e |- .+ = ( +g ` G ) $.
    $( Closure of the operation of a magma.  (Contributed by Richard Penner,
       22-Sep-2019.) $)
    mgmclNEW $p |- ( ( G e. MagmaNEW /\ X e. B /\ Y e. B ) -> ( X .+ Y ) e. B ) $=
      cG cmgmNEW wcel cX cB wcel cY cB wcel cX cY c.pl co cB wcel cG cmgmNEW
      wcel va cv vb cv c.pl co cB wcel vb cB wral va cB wral cX cB wcel cY cB
      wcel wa cX cY c.pl co cB wcel cG cmgmNEW wcel va cv vb cv c.pl co cB wcel
      vb cB wral va cB wral cB c.pl cG va vb mgmclNEW.g mgmclNEW.b mgmclNEW.p
      ismgmNEW biimpi va cv vb cv c.pl co cB wcel cX cY c.pl co cB wcel cX vb
      cv c.pl co cB wcel va vb cX cY cB cB va cv cX wceq va cv vb cv c.pl co cX
      vb cv c.pl co cB va cv cX vb cv c.pl oveq1 eleq1d vb cv cY wceq cX vb cv
      c.pl co cX cY c.pl co cB vb cv cY cX c.pl oveq2 eleq1d rspc2v mpan9 3impb
      $.

  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                   Monoids (additional)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Definition and basic properties (additional)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${

    $( A monoid is a magma. $)
    mndmgm $p |- ( G e. Mnd -> G e. MagmaNEW ) $= ? $.

  $}
