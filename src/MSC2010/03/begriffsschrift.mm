$[ set.mm $]

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

  $( The case in which ` ps ` is denied, ` ph ` is affirmed, and ` ps ` is
     affirmed is excluded.  This is evident since ` ps ` cannot at the same
     time be denied and affirmed.

     Axiom 1 of [Frege1879] p. ?.  Identical to ~ ax-1 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (New usage is discouraged.) $)
  frege1 $p |- ( ps -> ( ph -> ps ) ) $=
    wps wph ax-1 $.
  $( $j restatement 'frege1' of 'ax-1'; $)

  ${
    frege1just1.1 $e |- th $.
    frege1just1.2 $e |- ta $.
    frege1just1.3 $e |- -. et $.
    $( Justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just1 $p |- -. ( th -> ( ta -> et ) ) $=
    wta wet wi wn wth wta wet wi wi wn wet wn wta wet wi wn frege1just1.3 wta
    wet wn wta wet wi wn wi frege1just1.2 wta wet mth8 ax-mp ax-mp wth wta wet
    wi wn wth wta wet wi wi wn wi frege1just1.1 wth wta wet wi mth8 ax-mp ax-mp
    $.
  $}

  ${
    frege1just2.1 $e |- th $.
    $( Justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just2 $p |- ( ps -> ( ph -> th ) ) $=
    wph wth wi wps wth wph frege1just2.1 a1i a1i $.
  $}

  ${
    frege1just3.1 $e |- -. et $.
    $( Justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just3 $p |- ( ps -> ( et -> ph ) ) $=
    wet wph wi wps wet wph frege1just3.1 pm2.21i a1i $.
    $( Justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just4 $p |- ( et -> ( ps -> ph ) ) $=
    wet wps wph wi frege1just3.1 pm2.21i $.
  $}

  $( If a proposition ` ch ` is a neccessary consequence of two propostions
     ` ph ` and ` ps ` and on of those, ` ph ` , is in turn a necessary
     consequence of the other, ` ps ` , then the proposition ` ch ` is a
     necessary consequence of the latter one, ` ps ` , alone.

     Axiom 2 of [Frege1879] p. ?.  Identical to ~ ax-2 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (New usage is discouraged.) $)
  frege2 $p |- ( ( ps -> ( ph -> ch ) )
                 -> ( ( ps -> ph ) -> ( ps -> ch ) ) ) $=
    wps wph wch ax-2 $.
  $( $j restatement 'frege2' of 'ax-2'; $)

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr1 $p |- ( ps -> ( ph -> ( ch -> ph ) ) ) $=
    wph wch wph wi wi wps wph wch wph wi wi wi wph wch ax-1 wph wch wph wi wi
    wps ax-1 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr2 $p |- ( ( ( ps -> ( ph -> ch ) ) -> ( ps -> ph ) ) ->
              ( ( ps -> ( ph -> ch ) ) -> ( ps -> ch ) ) ) $=
    wps wph wch wi wi wps wph wi wps wch wi wi wi wps wph wch wi wi wps wph wi
    wi wps wph wch wi wi wps wch wi wi wi wps wph wch ax-2 wps wph wch wi wi
    wps wph wi wps wch wi ax-2 ax-mp $.
  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr4 $p |- ( ( ph -> ( ( ps -> ph ) -> ch ) ) -> ( ph -> ch ) ) $=
  wph wps wph wi wch wi wi wph wps wph wi wi wi wph wps wph wi wch wi wi wph
  wch wi wi wph wph wps wph wi wch wi wi wps fr1 wps wph wi wph wch fr2 ax-mp
  $.
  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr5 $p |- ( ( ps -> ph ) -> ( ps -> ( ch -> ph ) ) ) $=
    wps wph wch wph wi wi wi wps wph wi wps wch wph wi wi wi wph wps wch fr1
    wps wph wch wph wi ax-2 ax-mp $.

  $( More general statement than ~ frege3 or ~ frege4 .

     It would be more natural to prove from ~ a1i and ~ ax-2 in Metamath.
     (Contributed by Richard Penner, 1-Oct-2019.) $)
  fr3 $p |- ( ps ->
              ( ( ph -> ( ch -> th ) )
                -> ( ( ph -> ch ) -> ( ph -> th ) ) ) ) $=
    wph wch wth wi wi wph wch wi wph wth wi wi wi wps wph wch wth wi wi wph wch
    wi wph wth wi wi wi wi wph wch wth ax-2 wph wch wth wi wi wph wch wi wph
    wth wi wi wi wps ax-1 ax-mp $.

  $( Add antecedent to ~ ax-2 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege3 $p |- ( ( ph -> ch )
                 -> ( ( ps -> ( ph -> ch ) )
                      -> ( ( ps -> ph ) -> ( ps -> ch ) ) ) ) $=
      wps wph wch wi wi wps wph wi wps wch wi wi wi wph wch wi wps wph wch wi
      wi wps wph wi wps wch wi wi wi wi wps wph wch ax-2 wps wph wch wi wi wps
      wph wi wps wch wi wi wi wph wch wi ax-1 ax-mp $.

  $( Add a different antecedent to ~ ax-2 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege4 $p |- ( ( ( ps -> ph ) -> ( ch -> ( ps -> ph ) ) )
                 -> ( ( ps -> ph ) -> ( ( ch -> ps ) -> ( ch -> ph ) ) ) ) $=
    wps wph wi wch wps wph wi wi wch wps wi wch wph wi wi wi wi wps wph wi wch
    wps wph wi wi wi wps wph wi wch wps wi wch wph wi wi wi wi wps wch wph
    frege3 wps wph wi wch wps wph wi wi wch wps wi wch wph wi wi ax-2 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege5 $p |- ( ( ps -> ph ) -> ( ( ch -> ps ) -> ( ch -> ph ) ) ) $=
    wps wph wi wch wps wph wi wi wi wps wph wi wch wps wi wch wph wi wi wi wps
    wph wi wch ax-1 wph wps wch frege4 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege6 $p |- ( ( ps -> ( ph -> ch ) )
                 -> ( ps -> ( ( th -> ph ) -> ( th -> ch ) ) ) ) $=
  wph wch wi wth wph wi wth wch wi wi wi wps wph wch wi wi wps wth wph wi wth
  wch wi wi wi wi wch wph wth frege5 wth wph wi wth wch wi wi wph wch wi wps
  frege5 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege7 $p |- ( ( ps -> ph )
                 -> ( ( ch -> ( th -> ps ) ) -> ( ch -> ( th -> ph ) ) ) ) $=
  wps wph wi wth wps wi wth wph wi wi wi wps wph wi wch wth wps wi wi wch wth
  wph wi wi wi wi wph wps wth frege5 wth wps wi wps wph wi wth wph wi wch
  frege6 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ pm2.04 which can be proved
     from only ~ ax-mp , ~ ax-1 , and ~ ax-2 .

     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege8 $p |- ( ( ps -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) ) $=
  wps wph wch pm2.04 $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ pm2.04 .  See
     http://us.metamath.org/mmsolitaire/pmproofs.txt

     (Contributed by Richard Penner, 1-Oct-2019.)
     (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  frege8ALT $p |- ( ( ps -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) ) $=
    wps wph wch wi wi wph wps wph wi wps wch wi wi wi wi wps wph wch wi wi wph
    wps wch wi wi wi wps wph wch wi wi wps wph wi wps wch wi wi wi wps wph wch
    wi wi wph wps wph wi wps wch wi wi wi wi wps wph wch ax-2 wps wph wi wps
    wch wi wi wps wph wch wi wi wph fr5 ax-mp wps wph wch wi wi wph wps wph wi
    wps wch wi wi wi wph wps wch wi wi wi wi wps wph wch wi wi wph wps wph wi
    wps wch wi wi wi wi wps wph wch wi wi wph wps wch wi wi wi wi wph wps wph
    wi wps wch wi wi wi wph wps wch wi wi wi wps wph wch wi wi wph wps wph wi
    wps wch wi wi wi wph wps wch wi wi wi wi wph wps wps wch wi fr4 wph wps wph
    wi wps wch wi wi wi wph wps wch wi wi wi wps wph wch wi wi ax-1 ax-mp wps
    wph wch wi wi wph wps wph wi wps wch wi wi wi wph wps wch wi wi ax-2 ax-mp
    ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. This proposition differs from ~ frege5 only
     in an unessential way.

     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege9 $p |- ( ( ps -> ph ) -> ( ( ph -> ch ) -> ( ps -> ch ) ) ) $=
  wph wch wi wps wph wi wps wch wi wi wi wps wph wi wph wch wi wps wch wi wi wi
  wch wph wps frege5 wps wph wi wph wch wi wps wch wi frege8 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege10 $p |- ( ( ( ps -> ( ph -> ch ) ) -> th )
                -> ( ( ph -> ( ps -> ch ) ) -> th ) ) $=
  wph wps wch wi wi wps wph wch wi wi wi wps wph wch wi wi wth wi wph wps wch
  wi wi wth wi wi wps wph wch frege8 wps wph wch wi wi wph wps wch wi wi wth
  frege9 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege11 $p |- ( ( ( ps -> ph ) -> ch ) -> ( ph -> ch ) ) $=
    wph wps wph wi wi wps wph wi wch wi wph wch wi wi wph wps ax-1 wps wph wi
    wph wch frege9 ax-mp $.

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
