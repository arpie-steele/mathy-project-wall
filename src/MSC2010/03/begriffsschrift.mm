$[ set.mm $]

$(
                             ~~ PUBLIC DOMAIN ~~
  This work is waived of all rights, including copyright, according to the CC0
  Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/
$)

$( Numbered propositions from [Frege1879] . 1, 2, 8, 28, 31, 41, 52,
   and 54 are considered "core" or axioms. However, 8 can be derived
   from 1 and 2, see ~ frege8ALT .
$)

$(
###############################################################################
            CLASSICAL FIRST-ORDER LOGIC WITH EQUALITY
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
     Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( The case in which ` ph ` is denied, ` ps ` is affirmed, and ` ph ` is
     affirmed is excluded.  This is evident since ` ps ` cannot at the same
     time be denied and affirmed.

     Axiom 1 of [Frege1879] p. ?.  Identical to ~ ax-1 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (New usage is discouraged.) $)
  frege1 $p |- ( ph -> ( ps -> ph ) ) $=
    wph wps ax-1 $.
  $( $j restatement 'frege1' of 'ax-1'; $)

  ${
    frege1just1.1 $e |- ph $.
    frege1just1.2 $e |- ps $.
    frege1just1.3 $e |- -. ch $.
    $( Justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just1 $p |- -. ( ph -> ( ps -> ch ) ) $=
    wps wch wi wn wph wps wch wi wi wn wch wn wps wch wi wn frege1just1.3 wps
    wch wn wps wch wi wn wi frege1just1.2 wps wch mth8 ax-mp ax-mp wph wps wch
    wi wn wph wps wch wi wi wn wi frege1just1.1 wph wps wch wi mth8 ax-mp ax-mp
    $.
  $}

  ${
    frege1just2.1 $e |- ch $.
    $( Justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just2 $p |- ( ph -> ( ps -> ch ) ) $=
    wps wch wi wph wch wps frege1just2.1 a1i a1i $.
  $}

  ${
    frege1just3.1 $e |- -. ps $.
    $( Justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just3 $p |- ( ph -> ( ps -> ch ) ) $=
    wps wch wi wph wps wch frege1just3.1 pm2.21i a1i $.
  $}

  ${
    frege1just4.1 $e |- -. ph $.
    $( Justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just4 $p |- ( ph -> ( ps -> ch ) ) $=
    wph wps wch wi frege1just4.1 pm2.21i $.
  $}

  $( If a proposition ` ch ` is a neccessary consequence of two propostions
     ` ps ` and ` ph ` and on of those, ` ps ` , is in turn a necessary
     consequence of the other, ` ph ` , then the proposition ` ch ` is a
     necessary consequence of the latter one, ` ph ` , alone.

     Axiom 2 of [Frege1879] p. ?.  Identical to ~ ax-2 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (New usage is discouraged.) $)
  frege2 $p |- ( ( ph -> ( ps -> ch ) )
                 -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    wph wps wch ax-2 $.
  $( $j restatement 'frege2' of 'ax-2'; $)

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr1 $p |- ( ph -> ( ps -> ( ch -> ps ) ) ) $=
    wps wch wps wi wi wph wps wch wps wi wi wi wps wch ax-1 wps wch wps wi wi
    wph ax-1 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr2 $p |- ( ( ( ph -> ( ps -> ch ) ) -> ( ph -> ps ) ) ->
              ( ( ph -> ( ps -> ch ) ) -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi wi wph wps wch wi wi wph wps wi
    wi wph wps wch wi wi wph wch wi wi wi wph wps wch ax-2 wph wps wch wi wi
    wph wps wi wph wch wi ax-2 ax-mp $.

  $( More general statement than ~ frege3 .

     It would be more natural to prove from ~ a1i and ~ ax-2 in Metamath.
     (Contributed by Richard Penner, 1-Oct-2019.) $)
  fr3 $p |- ( ph ->
              ( ( ps -> ( ch -> th ) )
                -> ( ( ps -> ch ) -> ( ps -> th ) ) ) ) $=
    wps wch wth wi wi wps wch wi wps wth wi wi wi wph wps wch wth wi wi wps wch
    wi wps wth wi wi wi wi wps wch wth ax-2 wps wch wth wi wi wps wch wi wps
    wth wi wi wi wph ax-1 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr4 $p |- ( ( ph -> ( ( ps -> ph ) -> ch ) ) -> ( ph -> ch ) ) $=
    wph wps wph wi wch wi wi wph wps wph wi wi wi wph wps wph wi wch wi wi wph
    wch wi wi wph wps wph wi wch wi wi wph wps fr1 wph wps wph wi wch fr2 ax-mp
    $.
  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr5 $p |- ( ( ps -> ph ) -> ( ps -> ( ch -> ph ) ) ) $=
    wps wph wch wph wi wi wi wps wph wi wps wch wph wi wi wi wps wph wch fr1
    wps wph wch wph wi ax-2 ax-mp $.

  $( Add antecedent to ~ ax-2 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege3 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( ph -> ps ) )
                      -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
      wch wph wps wi wi wch wph wi wch wps wi wi wi wph wps wi wch wph wps wi
      wi wch wph wi wch wps wi wi wi wi wch wph wps ax-2 wch wph wps wi wi wch
      wph wi wch wps wi wi wi wph wps wi ax-1 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege4 $p |- ( ( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) )
                 -> ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
    wph wps wi wch wph wps wi wi wch wph wi wch wps wi wi wi wi wph wps wi wch
    wph wps wi wi wi wph wps wi wch wph wi wch wps wi wi wi wi wph wps wch
    frege3 wph wps wi wch wph wps wi wi wch wph wi wch wps wi wi ax-2 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege5 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    wph wps wi wch wph wps wi wi wi wph wps wi wch wph wi wch wps wi wi wi wph
    wps wi wch ax-1 wph wps wch frege4 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege6 $p |- ( ( ph -> ( ps -> ch ) )
                 -> ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) ) $=
    wps wch wi wth wps wi wth wch wi wi wi wph wps wch wi wi wph wth wps wi wth
    wch wi wi wi wi wps wch wth frege5 wps wch wi wth wps wi wth wch wi wi wph
    frege5 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege7 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( th -> ph ) ) -> ( ch -> ( th -> ps ) ) ) ) $=
    wph wps wi wth wph wi wth wps wi wi wi wph wps wi wch wth wph wi wi wch wth
    wps wi wi wi wi wph wps wth frege5 wph wps wi wth wph wi wth wps wi wch
    frege6 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ pm2.04 which can be proved
     from only ~ ax-mp , ~ ax-1 , and ~ ax-2 .

     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege8 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
  wph wps wch pm2.04 $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ pm2.04 .  See
     http://us.metamath.org/mmsolitaire/pmproofs.txt

     (Contributed by Richard Penner, 1-Oct-2019.)
     (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  frege8ALT $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wps wph wps wi wph wch wi wi wi wi wph wps wch wi wi wps
    wph wch wi wi wi wph wps wch wi wi wph wps wi wph wch wi wi wi wph wps wch
    wi wi wps wph wps wi wph wch wi wi wi wi wph wps wch ax-2 wph wps wi wph
    wch wi wi wph wps wch wi wi wps fr5 ax-mp wph wps wch wi wi wps wph wps wi
    wph wch wi wi wi wps wph wch wi wi wi wi wph wps wch wi wi wps wph wps wi
    wph wch wi wi wi wi wph wps wch wi wi wps wph wch wi wi wi wi wps wph wps
    wi wph wch wi wi wi wps wph wch wi wi wi wph wps wch wi wi wps wph wps wi
    wph wch wi wi wi wps wph wch wi wi wi wi wps wph wph wch wi fr4 wps wph wps
    wi wph wch wi wi wi wps wph wch wi wi wi wph wps wch wi wi ax-1 ax-mp wph
    wps wch wi wi wps wph wps wi wph wch wi wi wi wps wph wch wi wi ax-2 ax-mp
    ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. This proposition differs from ~ frege5 only
     in an unessential way.  Identical to ~ imim1 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege9 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wps wch wph frege5 wps wch wi wph wps wi wph wch wi frege8 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Could also be proved from ~ pm2.04
     and ~ imim1 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege10 $p |- ( ( ( ph -> ( ps -> ch ) ) -> th )
                -> ( ( ps -> ( ph -> ch ) ) -> th ) ) $=
    wps wph wch wi wi wph wps wch wi wi wi wph wps wch wi wi wth wi wps wph wch
    wi wi wth wi wi wps wph wch frege8 wps wph wch wi wi wph wps wch wi wi wth
    frege9 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ jarr .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege11 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    wps wph wps wi wi wph wps wi wch wi wps wch wi wi wps wph ax-1 wps wph wps
    wi wch frege9 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. $)

  $( PLEASE PUT DESCRIPTION HERE. $)

  $( PLEASE PUT DESCRIPTION HERE. $)

  $( PLEASE PUT DESCRIPTION HERE. $)

  $( PLEASE PUT DESCRIPTION HERE. $)

  $( PLEASE PUT DESCRIPTION HERE. $)

  $( PLEASE PUT DESCRIPTION HERE. $)




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Miscellaneous theorems of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
