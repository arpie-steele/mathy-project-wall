$[ set.mm $]

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

  $( Extend class notation with the class of all magmas. $)
  cmgmNEW $a class MagmaNEW $.

$( df-gsum can be used to map words to elements of a magma. See gsumval2a $)

$( mndcl proves a Mnd is closed under the binary operation, thus a magma. $)
  ${

    $d b g x y $.
    $( Definition of a magma.  A magma is a set equipped with an everywhere
       defined internal operation ( see ~ mgmclNEW ). $)
    df-mgmNEW $a |- MagmaNEW = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ].
A. x e. b A. y e. b ( x p y ) e. b } $.
  $}

  ${
    dfmgm2 $p |- MagmaNEW = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ].
p : ( b X. b ) --> b }
  $}

  ${

    $d a b g v p B $.  $d a b g v p G $.  $d a b g v p .+ $.
    ismgmNEW.g $e |- G e. _V $.
    ismgmNEW.b $e |- B = ( Base ` G ) $.
    ismgmNEW.p $e |- .+ = ( +g ` G ) $.
    $( The predicate "is a magma."
       (Contributed by Richard Penner, 21-Sep-2019.) $)
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
    $d a b B $.
    $d a b G $.
    $d a b .+ $.
    $d a b X $.
    $d b Y $.
    mgmclNEW.g $e |- G e. _V $.
    mgmclNEW.b $e |- B = ( Base ` G ) $.
    mgmclNEW.p $e |- .+ = ( +g ` G ) $.

    $( Closure of the operation of a magma.
       (Contributed by Richard Penner, 22-Sep-2019.) $)
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
