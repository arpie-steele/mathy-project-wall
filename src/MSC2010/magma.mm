$( df-gsum can be used to map words to elements of a magma. See gsumval2a $)

$( mndcl proves a Mnd is closed under the binary operation, thus a magma. $)

${
$d u w x B $.  $d u w x .+ $.
$( mgmidmo is a demonstration that the two-sided identity, u, of any binop .+ is unique if it exists $)

$( mgmidmo $p |- E* u e. B A. x e. B ( ( u .+ x ) = x /\ ( x .+ u ) = x ) $= ? $. $)

$}

${
$d e x y .+ $.  $d e x y .0. $.  $d e x y B $.  $d e x y G $.  $d x X $.
$d e x y U $.
mndidcl.b $e |- B = ( Base ` G ) $.
mndidcl.o $e |- .0. = ( 0g ` G ) $.
${
mgmidcl.p $e |- .+ = ( +g ` G ) $.
mgmidcl.e $e |- ( ph -> E. e e. B A. x e. B ( ( e .+ x ) = x /\ ( x .+ e ) = x ) ) $.
$( The identity element of a magma, if it exists, belongs to the base set.   $)
$( ismgmid $p |- ( ph -> ( ( U e. B /\
A. x e. B ( ( U .+ x ) = x /\ ( x .+ U ) = x ) ) <-> .0. = U ) ) $= ? $. $)


$c MagmaNEW $.
$( Extend class notation with the class of all magmas. $)
cmgmNEW $a class MagmaNEW $.

${

$d b g x y $.
$( Definition of a magma. A magma is a set equipped with an everywhere
       defined internal operation ( see ~ mgmclNEW ). 
df-mgmNEW $a |- MagmaNEW = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ].
A. x e. b A. y e. b ( x p y ) e. b } $.

$}

${

    $d a b B $.
    $d a b G $.
    $d a b .+ $.

    ismgmNEW.b $e |- B = ( Base ` G ) $.
    ismgmNEW.p $e |- .+ = ( +g ` G ) $.

    $( The predicate "is a magma." $)
    ismgmNEW |- ( G e. MagmaNEW <-> A. a e. B A. b e. B ( a .+ b ) e. B ) $= ? $.

$}

${

    $d x y B $.
    $d x y G $.
    $d x y X $.
    $d x y Y $.
    $d x y .+ $.

    mgmclNEW.b $e |- B = ( Base ` G ) $.
    mgmclNEW.p $e |- .+ = ( +g ` G ) $.

    $( Closure of the operation of a magma. $)
    mgmclNEW $p |- ( ( G e. MagmaNEW /\ X e. B /\ Y e. B ) -> ( X .+ Y ) e. B ) $= ? $.

}$
