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

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr6 $p |- ( ph -> ( ( ps -> ( ( ch -> ps ) -> th ) ) -> ( ps -> th ) ) ) $=
    wps wch wps wi wth wi wi wps wth wi wi wph wps wch wps wi wth wi wi wps wth
    wi wi wi wps wch wth fr4 wps wch wps wi wth wi wi wps wth wi wi wph ax-1
    ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr7 $p |- ( ( ph -> ( ps -> ch ) )
              -> ( th -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi wi wph wps wch wi wi wth wph wps
    wi wph wch wi wi wi wi wph wps wch ax-2 wph wps wi wph wch wi wi wph wps
    wch wi wi wth fr5 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr8 $p |- ( ( ph -> ( ps -> ( ( ch -> ps ) -> th ) ) )
              -> ( ph -> ( ps -> th ) ) )  $=
    wph wps wch wps wi wth wi wi wps wth wi wi wi wph wps wch wps wi wth wi wi
    wi wph wps wth wi wi wi wph wps wch wth fr6 wph wps wch wps wi wth wi wi
    wps wth wi ax-2 ax-mp $.


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
    wph wch wi wi wi wph wps wch wps fr7 wph wps wch wi wi wps wph wph wch wi
    fr8 ax-mp $.

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
  frege12 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege13 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege14 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege15 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege16 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege17 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege18 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege19 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege20 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege21 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege22 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege23 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege24 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege25 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege26 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege27 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. 
     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege28 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    wph wps con3th $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege29 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege30 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. 
     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege31 $p |- ( -. -. ph -> ph ) $=
    wph notnot2 $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege32 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege33 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege34 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege35 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege36 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege37 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege38 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege39 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege40 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. 
     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege41 $p |- ( ph -> -. -. ph ) $=
    wph notnot1 $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege42 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege43 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege44 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege45 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege46 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege47 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege48 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege49 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege50 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege51 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. 
     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege52a $p |- ( A = B -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) $=
    wph vx cA cB dfsbcq $.

  $( PLEASE PUT DESCRIPTION HERE. 
     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege52b $p |- ( A = B -> ( F ` A ) = ( F ` B ) ) $=
    cA cB cF fveq2 $.

  ${ 
    $d ph ch $.  $d ph th $.  $d ps ch $.  $d ps th $.
    $( PLEASE PUT DESCRIPTION HERE. 
       (Contributed by Richard Penner, 2-Oct-2019.) $)
    frege52c $p |- ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                     -> -. ( ( -. ( ( ph -> ch ) -> -. ( -. ph -> th ) )
                     -> -. ( ( ps -> ch ) -> -. ( -. ps -> th ) ) )
                     -> -. ( -. ( ( ps -> ch ) -> -. ( -. ps -> th ) )
                     -> -. ( ( ph -> ch ) -> -. ( -. ph -> th ) ) ) ) ) $=
      wph wps wi wps wph wi wn wi wn wph wps wb wph wch wi wph wn wth wi wn wi
      wn wps wch wi wps wn wth wi wn wi wn wi wps wch wi wps wn wth wi wn wi wn
      wph wch wi wph wn wth wi wn wi wn wi wn wi wn wph wps wb wph wps wi wps
      wph wi wn wi wn wph wps wb wph wps wi wps wph wi wa wph wps wi wps wph wi
      wn wi wn wph wps dfbi2 wph wps wi wps wph wi df-an bitri biimpri wph wps
      wb wph wch wi wph wn wth wi wn wi wn wps wch wi wps wn wth wi wn wi wn wb
      wph wch wi wph wn wth wi wn wi wn wps wch wi wps wn wth wi wn wi wn wi
      wps wch wi wps wn wth wi wn wi wn wph wch wi wph wn wth wi wn wi wn wi wn
      wi wn wph wps wb wph wch wi wph wn wth wi wn wi wn wps wch wi wps wn wth
      wi wa wps wch wi wps wn wth wi wn wi wn wph wch wi wph wn wth wi wn wi wn
      wph wch wi wph wn wth wi wa wph wps wb wps wch wi wps wn wth wi wa wph
      wch wi wph wn wth wi df-an wph wps wb wph wch wi wps wch wi wph wn wth wi
      wps wn wth wi wph wps wch imbi1 wph wps wb wph wn wps wn wb wph wn wth wi
      wps wn wth wi wb wph wps wb wph wn wps wn wb wph wps notbi biimpi wph wn
      wps wn wth imbi1 syl anbi12d syl5bbr wps wch wi wps wn wth wi df-an
      syl6bb wph wch wi wph wn wth wi wn wi wn wps wch wi wps wn wth wi wn wi
      wn wb wph wch wi wph wn wth wi wn wi wn wps wch wi wps wn wth wi wn wi wn
      wi wps wch wi wps wn wth wi wn wi wn wph wch wi wph wn wth wi wn wi wn wi
      wa wph wch wi wph wn wth wi wn wi wn wps wch wi wps wn wth wi wn wi wn wi
      wps wch wi wps wn wth wi wn wi wn wph wch wi wph wn wth wi wn wi wn wi wn
      wi wn wph wch wi wph wn wth wi wn wi wn wps wch wi wps wn wth wi wn wi wn
      dfbi2 wph wch wi wph wn wth wi wn wi wn wps wch wi wps wn wth wi wn wi wn
      wi wps wch wi wps wn wth wi wn wi wn wph wch wi wph wn wth wi wn wi wn wi
      df-an bitri sylib syl $.

  $}

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege53 $p |- ( ph -> -. ph ) $= ? $.

  $( Reflexive equality of classes. 
     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege54a $p |- A = A $=
    cA eqid $.

  $( Reflexive equality of logical propositions. 
     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege54b $p |- -. ( ( ph -> ph ) -> -. ( ph -> ph ) ) $=
    wph wph wi wph wph wi wa wph wph wi wph wph wi wn wi wn wph wph wb wph wph
    wi wph wph wi wa wph biid wph wph wb wph wph wi wph wph wi wa wph wph dfbi2
    biimpi ax-mp wph wph wi wph wph wi wa wph wph wi wph wph wi wn wi wn wph
    wph wi wph wph wi df-an biimpi ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege55 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege56 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege57 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege58 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege59 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege60 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege61 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege62 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege63 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege64 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege65 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege66 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege67 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege68 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege69 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege70 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege71 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege72 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege73 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege74 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege75 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege76 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege77 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege78 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege79 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege80 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege81 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege82 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege83 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege84 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege85 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege86 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege87 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege88 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege89 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege90 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege91 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege92 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege93 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege94 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege95 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege96 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege97 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege98 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. $)
  frege99 $p |- ( ph -> -. ph ) $= ? $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Miscellaneous theorems of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
