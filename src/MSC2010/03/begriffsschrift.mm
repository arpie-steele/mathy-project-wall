$[ set.mm $]

$(
                             ~~ PUBLIC DOMAIN ~~
  This work is waived of all rights, including copyright, according to the CC0
  Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Mathbox for Richard Penner
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Propositions from _Begriffschift_
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Numbered propositions from [Frege1879] . ~ frege1 , ~ frege2 ,
   ~ frege8 , ~ frege28 , ~ frege31 , ~ frege41 , ~ frege52 , and
   ~ frege54 are considered "core" or axioms. However, at least
   ~ frege8 can be derived from ~ frege1 and ~ frege2 , see
   ~ frege8ALT .
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter II
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The case in which ` ph ` is denied, ` ps ` is affirmed, and ` ph ` is
     affirmed is excluded.  This is evident since ` ph ` cannot at the same
     time be denied and affirmed.

     Axiom 1 of [Frege1879] p. 26.  Identical to ~ ax-1 .

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

     Axiom 2 of [Frege1879] p. 26.  Identical to ~ ax-2 .

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
  $( PLEASE PUT DESCRIPTION HERE. Alternate proof for ~ frege24 .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege24ALT $p |- ( ( ps -> ph ) -> ( ps -> ( ch -> ph ) ) ) $=
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
    wch wi wi wth frege24ALT ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  fr8 $p |- ( ( ph -> ( ps -> ( ( ch -> ps ) -> th ) ) )
              -> ( ph -> ( ps -> th ) ) ) $=
    wph wps wch wps wi wth wi wi wps wth wi wi wi wph wps wch wps wi wth wi wi
    wi wph wps wth wi wi wi wph wps wch wth fr6 wph wps wch wps wi wth wi wi
    wps wth wi ax-2 ax-mp $.


  $( Add antecedent to ~ ax-2 .  Special case of ~ fr3 .

     Proposition 3 of [Frege1879] p. 29.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege3 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( ph -> ps ) )
                      -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
      wch wph wps wi wi wch wph wi wch wps wi wi wi wph wps wi wch wph wps wi
      wi wch wph wi wch wps wi wi wi wi wch wph wps ax-2 wch wph wps wi wi wch
      wph wi wch wps wi wi wi wph wps wi ax-1 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 4 of [Frege1879] p. 31.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege4 $p |- ( ( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) )
                 -> ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
    wph wps wi wch wph wps wi wi wch wph wi wch wps wi wi wi wi wph wps wi wch
    wph wps wi wi wi wph wps wi wch wph wi wch wps wi wi wi wi wph wps wch
    frege3 wph wps wi wch wph wps wi wi wch wph wi wch wps wi wi ax-2 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 5 of [Frege1879] p. 32.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege5 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    wph wps wi wch wph wps wi wi wi wph wps wi wch wph wi wch wps wi wi wi wph
    wps wi wch ax-1 wph wps wch frege4 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 6 of [Frege1879] p. 33.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege6 $p |- ( ( ph -> ( ps -> ch ) )
                 -> ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) ) $=
    wps wch wi wth wps wi wth wch wi wi wi wph wps wch wi wi wph wth wps wi wth
    wch wi wi wi wi wps wch wth frege5 wps wch wi wth wps wi wth wch wi wi wph
    frege5 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 7 of [Frege1879] p. 34.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege7 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( th -> ph ) ) -> ( ch -> ( th -> ps ) ) ) ) $=
    wph wps wi wth wph wi wth wps wi wi wi wph wps wi wch wth wph wi wi wch wth
    wps wi wi wi wi wph wps wth frege5 wph wps wi wth wph wi wth wps wi wch
    frege6 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ pm2.04 which can be proved
     from only ~ ax-mp , ~ ax-1 , and ~ ax-2 .

     Axiom 8 of [Frege1879] p. 35.

     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege8 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
  wph wps wch pm2.04 $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ pm2.04 .

     Proof follows closely proof of ~ pm2.04 in
     ~ http://us.metamath.org/mmsolitaire/pmproofs.txt , but in the style of
     [Frege1879] .

     Axiom 8 of [Frege1879] p. 35.

     (Contributed by Richard Penner, 1-Oct-2019.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  frege8ALT $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wps wph wps wi wph wch wi wi wi wi wph wps wch wi wi wps
    wph wch wi wi wi wph wps wch wps fr7 wph wps wch wi wi wps wph wph wch wi
    fr8 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. This proposition differs from ~ frege5 only
     in an unessential way.  Identical to ~ imim1 .

     Proposition 9 of [Frege1879] p. 35.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege9 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wps wch wph frege5 wps wch wi wph wps wi wph wch wi frege8 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Could also be proved from ~ pm2.04 and
     ~ imim1 .

     Proposition 10 of [Frege1879] p. 36.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege10 $p |- ( ( ( ph -> ( ps -> ch ) ) -> th )
                -> ( ( ps -> ( ph -> ch ) ) -> th ) ) $=
    wps wph wch wi wi wph wps wch wi wi wi wph wps wch wi wi wth wi wps wph wch
    wi wi wth wi wi wps wph wch frege8 wps wph wch wi wi wph wps wch wi wi wth
    frege9 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ jarr .

     Proposition 11 of [Frege1879] p. 36.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege11 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    wps wph wps wi wi wph wps wi wch wi wps wch wi wi wps wph ax-1 wps wph wps
    wi wch frege9 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 12 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege12 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ph -> ( ch -> ( ps -> th ) ) ) ) $=
    wps wch wth wi wi wch wps wth wi wi wi wph wps wch wth wi wi wi wph wch wps
    wth wi wi wi wi wps wch wth frege8 wps wch wth wi wi wch wps wth wi wi wph
    frege5 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 13 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege13 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ch -> ( ph -> ( ps -> th ) ) ) ) $=
    wph wps wch wth wi wi wi wph wch wps wth wi wi wi wi wph wps wch wth wi wi
    wi wch wph wps wth wi wi wi wi wph wps wch wth frege12 wph wps wch wth wi
    wi wi wph wch wps wth wi frege12 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 14 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege14 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( ph -> ( th -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    wps wch wth wta wi wi wi wth wps wch wta wi wi wi wi wph wps wch wth wta wi
    wi wi wi wph wth wps wch wta wi wi wi wi wi wps wch wth wta frege13 wps wch
    wth wta wi wi wi wth wps wch wta wi wi wi wph frege5 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 15 of [Frege1879] p. 38.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege15 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    wph wps wch wth wta wi wi wi wi wph wth wps wch wta wi wi wi wi wi wph wps
    wch wth wta wi wi wi wi wth wph wps wch wta wi wi wi wi wi wph wps wch wth
    wta frege14 wph wps wch wth wta wi wi wi wi wph wth wps wch wta wi wi
    frege12 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 16 of [Frege1879] p. 38.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege16 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) ) $=
    wps wch wth wta wi wi wi wps wth wch wta wi wi wi wi wph wps wch wth wta wi
    wi wi wi wph wps wth wch wta wi wi wi wi wi wps wch wth wta frege12 wps wch
    wth wta wi wi wi wps wth wch wta wi wi wi wph frege5 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 17 of [Frege1879] p. 39.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege17 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ps -> ( ch -> ( ph -> th ) ) ) ) $=
    wph wps wch wth wi wi wi wps wph wch wth wi wi wi wi wph wps wch wth wi wi
    wi wps wch wph wth wi wi wi wi wph wps wch wth wi frege8 wph wps wch wth wi
    wi wi wps wph wch wth frege16 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 18 of [Frege1879] p. 39.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege18 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( th -> ph ) -> ( ps -> ( th -> ch ) ) ) ) $=
    wph wps wch wi wi wth wph wi wth wps wch wi wi wi wi wph wps wch wi wi wth
    wph wi wps wth wch wi wi wi wi wph wps wch wi wth frege5 wph wps wch wi wi
    wth wph wi wth wps wch frege16 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 19 of [Frege1879] p. 39.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege19 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( ch -> th ) -> ( ph -> ( ps -> th ) ) ) ) $=
    wps wch wi wch wth wi wps wth wi wi wi wph wps wch wi wi wch wth wi wph wps
    wth wi wi wi wi wps wch wth frege9 wps wch wi wch wth wi wps wth wi wph
    frege18 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 20 of [Frege1879] p. 40.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege20 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( th -> ta ) -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    wps wch wth wi wi wth wta wi wps wch wta wi wi wi wi wph wps wch wth wi wi
    wi wth wta wi wph wps wch wta wi wi wi wi wi wps wch wth wta frege19 wps
    wch wth wi wi wth wta wi wps wch wta wi wi wph frege18 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 21 of [Frege1879] p. 40.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege21 $p |- ( ( ( ph -> ps ) -> ch )
                  -> ( ( ph -> th ) -> ( ( th -> ps ) -> ch ) ) )  $=
    wph wth wi wth wps wi wph wps wi wi wi wph wps wi wch wi wph wth wi wth wps
    wi wch wi wi wi wph wth wps frege9 wph wth wi wth wps wi wph wps wi wch
    frege19 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 22 of [Frege1879] p. 41.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege22 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )
                  -> ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) ) $=
    wps wch wth wta wet wi wi wi wi wps wch wta wth wet wi wi wi wi wi wph wps
    wch wth wta wet wi wi wi wi wi wph wps wch wta wth wet wi wi wi wi wi wi
    wps wch wth wta wet frege16 wps wch wth wta wet wi wi wi wi wps wch wta wth
    wet wi wi wi wi wph frege5 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 23 of [Frege1879] p. 42.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege23 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( ta -> ph )
                       -> ( ps -> ( ch -> ( ta -> th ) ) ) ) ) $=
    wph wps wch wth wi wi wi wta wph wi wps wta wch wth wi wi wi wi wi wph wps
    wch wth wi wi wi wta wph wi wps wch wta wth wi wi wi wi wi wph wps wch wth
    wi wta frege18 wph wps wch wth wi wi wi wta wph wi wps wta wch wth frege22
    ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ frege24ALT which
     was proved without relying on ~ frege8 .

     Proposition 24 of [Frege1879] p. 42.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege24 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    wph wps wi wch wph wps wi wi wi wph wps wi wph wch wps wi wi wi wph wps wi
    wch ax-1 wph wps wi wch wph wps frege12 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 25 of [Frege1879] p. 42.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege25 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    wps wch wi wps wth wch wi wi wi wph wps wch wi wi wph wps wth wch wi wi wi
    wi wps wch wth frege24 wps wch wi wps wth wch wi wi wph frege5 ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ idd .

     Proposition 26 of [Frege1879] p. 42.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege26 $p |- ( ph -> ( ps -> ps ) ) $=
    wps wph wps wi wi wph wps wps wi wi wps wph ax-1 wps wph wps frege8 ax-mp
    $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ id .

     Proposition 27 of [Frege1879] p. 43.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege27 $p |- ( ph -> ph ) $=
    wph wps wph wi wi wph wph wi wph wps ax-1 wph wps wph wi wi wph frege26
    ax-mp $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ con3th .

     Axiom 28 of [Frege1879] p. 43.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege28 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    wph wps con3th $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 29 of [Frege1879] p. 43. $)
  frege29 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 30 of [Frege1879] p. 44. $)
  frege30 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ notnot2 .

     Axiom 31 of [Frege1879] p. 44.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege31 $p |- ( -. -. ph -> ph ) $=
    wph notnot2 $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 32 of [Frege1879] p. 44. $)
  frege32 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 33 of [Frege1879] p. 44. $)
  frege33 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 34 of [Frege1879] p. 45. $)
  frege34 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 35 of [Frege1879] p. 45. $)
  frege35 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 36 of [Frege1879] p. 45. $)
  frege36 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 37 of [Frege1879] p. 46. $)
  frege37 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 38 of [Frege1879] p. 46. $)
  frege38 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 39 of [Frege1879] p. 46. $)
  frege39 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 40 of [Frege1879] p. 46. $)
  frege40 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ notnot1 .

     Axiom 41 of [Frege1879] p. 47.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege41 $p |- ( ph -> -. -. ph ) $=
    wph notnot1 $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 42 of [Frege1879] p. 47. $)
  frege42 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 43 of [Frege1879] p. 47. $)
  frege43 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 44 of [Frege1879] p. 47. $)
  frege44 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 45 of [Frege1879] p. 47. $)
  frege45 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 46 of [Frege1879] p. 48. $)
  frege46 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 47 of [Frege1879] p. 48. $)
  frege47 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 48 of [Frege1879] p. 49. $)
  frege48 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 49 of [Frege1879] p. 49. $)
  frege49 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 50 of [Frege1879] p. 49. $)
  frege50 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 51 of [Frege1879] p. 50. $)
  frege51 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ dfsbcq .

     Part of Axiom 52 of [Frege1879] p. 50.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege52a $p |- ( A = B -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) $=
    wph vx cA cB dfsbcq $.

  $( PLEASE PUT DESCRIPTION HERE. Identical to ~ fveq2 .

     Part of Axiom 52 of [Frege1879] p. 50.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege52b $p |- ( A = B -> ( F ` A ) = ( F ` B ) ) $=
    cA cB cF fveq2 $.

  $( PLEASE PUT DESCRIPTION HERE.

     Part of Axiom 52 of [Frege1879] p. 50.

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

  $( PLEASE PUT DESCRIPTION HERE.

     Part of Axiom 52 of [Frege1879] p. 50.

     (Contributed by Richard Penner, 3-Oct-2019.) $)
  frege52cALT $p |- ( ( ph <-> ps )
                        -> ( if- ( ph , ch , th )
                           <-> if- ( ps , ch , th ) ) ) $=
    wph wch wth wif wph wch wa wph wn wth wa wo wph wps wb wps wch wth wif wph
    wch wth bj-dfif2 wph wps wb wph wch wa wph wn wth wa wo wps wch wa wps wn
    wth wa wo wps wch wth wif wph wps wb wph wch wa wps wch wa wph wn wth wa
    wps wn wth wa wph wps wb wph wps wch wph wps wb id anbi1d wph wps wb wph wn
    wps wn wth wph wps wb wph wn wps wn wb wph wps notbi biimpi anbi1d orbi12d
    wps wch wth bj-dfif2 syl6bbr syl5bb $.


  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 53 of [Frege1879] p. 50. $)
  frege53 $p |- ( ph -> -. ph ) $= ? $.

  $( Reflexive equality of classes.

     Part of Axiom 54 of [Frege1879] p. 50.  Identical to ~ eqid .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege54a $p |- A = A $=
    cA eqid $.

  $( Reflexive equality of logical propositions.  Basically identical to
     ~ biid .

     Part of Axiom 54 of [Frege1879] p. 50.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege54b $p |- -. ( ( ph -> ph ) -> -. ( ph -> ph ) ) $=
    wph wph wi wph wph wi wa wph wph wi wph wph wi wn wi wn wph wph wb wph wph
    wi wph wph wi wa wph biid wph wph wb wph wph wi wph wph wi wa wph wph dfbi2
    biimpi ax-mp wph wph wi wph wph wi wa wph wph wi wph wph wi wn wi wn wph
    wph wi wph wph wi df-an biimpi ax-mp $.

  $( Reflexive equality of logical propositions.  Identical to ~ biid .

     Part of Axiom 54 of [Frege1879] p. 50.

     (Contributed by Richard Penner, 3-Oct-2019.) $)
  frege54bALT $p |- ( ph <-> ph ) $= wph biid $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 55 of [Frege1879] p. 50. $)
  frege55 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 56 of [Frege1879] p. 50. $)
  frege56 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 57 of [Frege1879] p. 51. $)
  frege57 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 58 of [Frege1879] p. 51. $)
  frege58 $p |- ( ph -> -. ph ) $= ? $.

  $( A kind of Aristotelian inference.

     Proposition 59 of [Frege1879] p. 51. $)
  frege59 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 60 of [Frege1879] p. 52. $)
  frege60 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 61 of [Frege1879] p. 52. $)
  frege61 $p |- ( ph -> -. ph ) $= ? $.

  $( A kind of Aristotelian inference.

     Proposition 62 of [Frege1879] p. 52. $)
  frege62 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 63 of [Frege1879] p. 52. $)
  frege63 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 64 of [Frege1879] p. 53. $)
  frege64 $p |- ( ph -> -. ph ) $= ? $.

  $( A kind of Aristotelian inference.

     Proposition 65 of [Frege1879] p. 53. $)
  frege65 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 66 of [Frege1879] p. 54. $)
  frege66 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 67 of [Frege1879] p. 54. $)
  frege67 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 68 of [Frege1879] p. 54. $)
  frege68 $p |- ( ph -> -. ph ) $= ? $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter III
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 69 of [Frege1879] p. 55. $)
  frege69 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 70 of [Frege1879] p. 58. $)
  frege70 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 71 of [Frege1879] p. 59. $)
  frege71 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 72 of [Frege1879] p. 59. $)
  frege72 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 73 of [Frege1879] p. 59. $)
  frege73 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 74 of [Frege1879] p. 60. $)
  frege74 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 75 of [Frege1879] p. 60. $)
  frege75 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 76 of [Frege1879] p. 60. $)
  frege76 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 77 of [Frege1879] p. 62. $)
  frege77 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 78 of [Frege1879] p. 63. $)
  frege78 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 79 of [Frege1879] p. 63. $)
  frege79 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 80 of [Frege1879] p. 63. $)
  frege80 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 81 of [Frege1879] p. 63. $)
  frege81 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 82 of [Frege1879] p. 64. $)
  frege82 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 83 of [Frege1879] p. 65. $)
  frege83 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 84 of [Frege1879] p. 65. $)
  frege84 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 85 of [Frege1879] p. 66. $)
  frege85 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 86 of [Frege1879] p. 66. $)
  frege86 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 87 of [Frege1879] p. 66. $)
  frege87 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 88 of [Frege1879] p. 67. $)
  frege88 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 89 of [Frege1879] p. 68. $)
  frege89 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 90 of [Frege1879] p. 68. $)
  frege90 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 91 of [Frege1879] p. 68. $)
  frege91 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 92 of [Frege1879] p. 69. $)
  frege92 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 93 of [Frege1879] p. 70. $)
  frege93 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 94 of [Frege1879] p. 70. $)
  frege94 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 95 of [Frege1879] p. 70. $)
  frege95 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 96 of [Frege1879] p. 71. $)
  frege96 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 97 of [Frege1879] p. 71. $)
  frege97 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 98 of [Frege1879] p. 71. $)
  frege98 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 99 of [Frege1879] p. 71. $)
  frege99 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 100 of [Frege1879] p. 72. $)
  frege100 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 101 of [Frege1879] p. 72. $)
  frege101 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 102 of [Frege1879] p. 72. $)
  frege102 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 103 of [Frege1879] p. 73. $)
  frege103 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 104 of [Frege1879] p. 73. $)
  frege104 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 105 of [Frege1879] p. 73. $)
  frege105 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 106 of [Frege1879] p. 73. $)
  frege106 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 107 of [Frege1879] p. 74. $)
  frege107 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 108 of [Frege1879] p. 74. $)
  frege108 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 109 of [Frege1879] p. 74. $)
  frege109 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 110 of [Frege1879] p. 75. $)
  frege110 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 111 of [Frege1879] p. 75. $)
  frege111 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 112 of [Frege1879] p. 76. $)
  frege112 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 113 of [Frege1879] p. 76. $)
  frege113 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 114 of [Frege1879] p. 76. $)
  frege114 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 115 of [Frege1879] p. 77. $)
  frege115 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 116 of [Frege1879] p. 77. $)
  frege116 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 117 of [Frege1879] p. 78. $)
  frege117 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 118 of [Frege1879] p. 78. $)
  frege118 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 119 of [Frege1879] p. 78. $)
  frege119 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 120 of [Frege1879] p. 78. $)
  frege120 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 121 of [Frege1879] p. 79. $)
  frege121 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 122 of [Frege1879] p. 79. $)
  frege122 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 123 of [Frege1879] p. 79. $)
  frege123 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 124 of [Frege1879] p. 80. $)
  frege124 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 125 of [Frege1879] p. 81. $)
  frege125 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 126 of [Frege1879] p. 81. $)
  frege126 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 127 of [Frege1879] p. 82. $)
  frege127 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 128 of [Frege1879] p. 83. $)
  frege128 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 129 of [Frege1879] p. 83. $)
  frege129 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 130 of [Frege1879] p. 84. $)
  frege130 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 131 of [Frege1879] p. 85. $)
  frege131 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 132 of [Frege1879] p. 86. $)
  frege132 $p |- ( ph -> -. ph ) $= ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 133 of [Frege1879] p. 86. $)
  frege133 $p |- ( ph -> -. ph ) $= ? $.
