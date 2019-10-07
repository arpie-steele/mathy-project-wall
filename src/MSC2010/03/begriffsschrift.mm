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

  $( Simplification of triple conjunction. Compare with ~ simp2 .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  simp2frege $p |- ( ph -> ( ps -> ( ch -> ps ) ) ) $=
    wps wch wps wi wi wph wps wch wps wi wi wi wps wch ax-1 wps wch wps wi wi
    wph ax-1 ax-mp $.

  $( More general statement than ~ frege3 . Like ~ ax-2 , it is
     essentially a closed form of ~ mpd , however it has an extra
     antecedent.

     It would be more natural to prove from ~ a1i and ~ ax-2 in Metamath.
     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege3gen $p |- ( ph
                    -> ( ( ps -> ( ch -> th ) )
                         -> ( ( ps -> ch ) -> ( ps -> th ) ) ) ) $=
    wps wch wth wi wi wps wch wi wps wth wi wi wi wph wps wch wth wi wi wps wch
    wi wps wth wi wi wi wi wps wch wth ax-2 wps wch wth wi wi wps wch wi wps
    wth wi wi wi wph ax-1 ax-mp $.

  $( Specialized form of ~ idd .

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  iddspfrege $p |- ( ( ph -> ps ) -> ( ph -> ph ) ) $=
    wph wps wph wi wi wph wps wi wph wph wi wi wph wps ax-1 wph wps wph ax-2
    ax-mp $.

  $( Double-use of ~ ax-2 .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  misc1frege $p |- ( ( ( ph -> ( ps -> ch ) ) -> ( ph -> ps ) )
                     -> ( ( ph -> ( ps -> ch ) ) -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi wi wph wps wch wi wi wph wps wi
    wi wph wps wch wi wi wph wch wi wi wi wph wps wch ax-2 wph wps wch wi wi
    wph wps wi wph wch wi ax-2 ax-mp $.

  $( Simplify when consequent is also third antecedent.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  simprlfrege $p |- ( ph -> ( ps -> ( ch -> ( th -> ch ) ) ) ) $=
    wps wch wth wch wi wi wi wph wps wch wth wch wi wi wi wi wps wch wth
    simp2frege wps wch wth wch wi wi wi wph ax-1 ax-mp $.

  $( Distribution with two unnecessary antecendents.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  misc3frege $p |- ( ph
                     -> ( ps
                          -> ( ( ch -> ( th -> ta ) )
                               -> ( ( ch -> th ) -> ( ch -> ta ) ) ) ) ) $=
    wps wch wth wta wi wi wch wth wi wch wta wi wi wi wi wph wps wch wth wta wi
    wi wch wth wi wch wta wi wi wi wi wi wps wch wth wta frege3gen wps wch wth
    wta wi wi wch wth wi wch wta wi wi wi wi wph ax-1 ax-mp $.

  $( Introducing an embedded antecedent.  Alternate proof for
     ~ frege24 .  Closed form for ~ a1d .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege24ALT $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    wph wps wch wps wi wi wi wph wps wi wph wch wps wi wi wi wph
    wps wch simp2frege wph wps wch wps wi ax-2 ax-mp $.

  ${
    a1dfrege.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent. Identical to ~ a1d .

       (Contributed by Richard Penner, 4-Oct-2019.) $)
    a1dfrege $p |- ( ph -> ( ch -> ps ) ) $=
      wph wps wi wph wch wps wi wi a1dfrege.1 wph wps wch frege24ALT ax-mp $.
  $}

  $( Simplify when consequent is also the first antecedent.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  simp1frege $p |- ( ph -> ( ps -> ( ch -> ph ) ) ) $=
    wph wch wph wi wi wph wps wch wph wi wi wi wph wch ax-1 wph wch wph wi wps
    frege24ALT ax-mp $.

  $( Deduction relatied to distribution.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  frege3gendist $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                        -> ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) ) $=
    wph wps wch wth wi wi wps wch wi wps wth wi wi wi wi wph wps wch wth wi wi
    wi wph wps wch wi wps wth wi wi wi wi wph wps wch wth frege3gen wph wps wch
    wth wi wi wps wch wi wps wth wi wi ax-2 ax-mp $.

  $( Elimination of a nested antecedent of special form.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp4frege $p |- ( ( ph -> ( ( ps -> ph ) -> ch ) ) -> ( ph -> ch ) ) $=
    wph wps wph wi wch wi wi wph wps wph wi wi wi wph wps wph wi wch wi wi wph
    wch wi wi wph wps wph wi wch wi wi wph wps simp2frege wph wps wph wi wch
    misc1frege ax-mp $.

  ${
    rp4fregei.1 $e |- ( ph -> ( ( ps -> ph ) -> ch ) ) $.
    $( More naturally proved in Metamath from ~ ax-1 and ~ mpd .

       (Contributed by RichardPenner, 5-Oct-2019.) $)
    rp4fregei $p |- ( ph -> ch ) $=
      wph wps wph wi wch wi wi wph wch wi rp4fregei.1 wph wps wch rp4frege
      ax-mp $.
  $}

  $( Distribute antecedent and add another.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp7frege $p |- ( ( ph -> ( ps -> ch ) )
              -> ( th -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi wi wph wps wch wi wi wth wph wps
    wi wph wch wi wi wi wi wph wps wch ax-2 wph wps wch wi wi wph wps wi wph
    wch wi wi wth frege24ALT ax-mp $.

  $( Elimination of a nested antecedent of special form.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp6frege $p |- ( ph
                   -> ( ( ps -> ( ( ch -> ps ) -> th ) ) -> ( ps -> th ) ) ) $=
    wps wch wps wi wth wi wi wps wth wi wi wph wps wch wps wi wth wi wi wps wth
    wi wi wi wps wch wth rp4frege wps wch wps wi wth wi wi wps wth wi wi wph
    ax-1 ax-mp $.

  $( Eliminate antecedent when it is implied by previous antecedent.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp8frege $p |- ( ( ph -> ( ps -> ( ( ch -> ps ) -> th ) ) )
                   -> ( ph -> ( ps -> th ) ) ) $=
    wph wps wch wps wi wth wi wi wps wth wi wi wi wph wps wch wps wi wth wi wi
    wi wph wps wth wi wi wi wph wps wch wth rp6frege wph wps wch wps wi wth wi
    wi wps wth wi ax-2 ax-mp $.


  $( Add antecedent to ~ ax-2 .  Special case of ~ frege3gen .

     Proposition 3 of [Frege1879] p. 29.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege3 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( ph -> ps ) )
                      -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
      wch wph wps wi wi wch wph wi wch wps wi wi wi wph wps wi wch wph wps wi
      wi wch wph wi wch wps wi wi wi wi wch wph wps ax-2 wch wph wps wi wi wch
      wph wi wch wps wi wi wi wph wps wi ax-1 ax-mp $.

  $( Special case of closed form of ~ a2d .

     Proposition 4 of [Frege1879] p. 31.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege4 $p |- ( ( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) )
                 -> ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
    wph wps wi wch wph wps wi wi wch wph wi wch wps wi wi wi wi wph wps wi wch
    wph wps wi wi wi wph wps wi wch wph wi wch wps wi wi wi wi wph wps wch
    frege3 wph wps wi wch wph wps wi wi wch wph wi wch wps wi wi ax-2 ax-mp $.

  ${
    a2dspfrege.1 $e |- ( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) ) $.
    $( Deduction distributing an embedded antecedent. Special case of ~ a2d .

       (Contributed by Richard Penner, 4-Oct-2019.) $)
    a2dspfrege $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
      wph wps wi wch wph wps wi wi wi wph wps wi wch wph wi wch wps wi wi wi
      a2dspfrege.1 wph wps wch frege4 ax-mp $.
  $}

  $( A closed form of ~ syl . Identical to ~ imim2 .

     Theorem *2.05 of [WhiteheadRussell] p. 100.

     Proposition 5 of [Frege1879] p. 32.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege5 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    wph wps wi wch wph wps wi wi wi wph wps wi wch wph wi wch wps wi wi wi wph
    wps wi wch ax-1 wph wps wch frege4 ax-mp $.

  $( A closed form of ~ imim2d which is a deduction adding nested antecedents.

     Proposition 6 of [Frege1879] p. 33.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege6 $p |- ( ( ph -> ( ps -> ch ) )
                 -> ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) ) $=
    wps wch wi wth wps wi wth wch wi wi wi wph wps wch wi wi wph wth wps wi wth
    wch wi wi wi wi wps wch wth frege5 wps wch wi wth wps wi wth wch wi wi wph
    frege5 ax-mp $.

  $( A closed form of ~ syl6 . The first antecedent is used to
     replace the consequent of the second antecedent.

     Proposition 7 of [Frege1879] p. 34.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege7 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( th -> ph ) ) -> ( ch -> ( th -> ps ) ) ) ) $=
    wph wps wi wth wph wi wth wps wi wi wi wph wps wi wch wth wph wi wi wch wth
    wps wi wi wi wi wph wps wth frege5 wph wps wi wth wph wi wth wps wi wch
    frege6 ax-mp $.

  $( Swap antecedents. Third axiom of [Frege1879] but identical to
     ~ pm2.04 which can be proved from only ~ ax-mp , ~ ax-1 , and
     ~ ax-2 .

     (Redundant) Axiom 8 of [Frege1879] p. 35.

     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege8 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
  wph wps wch pm2.04 $.

  $( Swap antecedents. Identical to ~ pm2.04 .

     Proof follows closely proof of ~ pm2.04 in
     ~ http://us.metamath.org/mmsolitaire/pmproofs.txt , but in the style of
     [Frege1879] .

     This demonstrates that Axiom 8 of [Frege1879] p. 35 is redundant.

     (Contributed by Richard Penner, 1-Oct-2019.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  frege8ALT $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wps wph wps wi wph wch wi wi wi wi wph wps wch wi wi wps
    wph wch wi wi wi wph wps wch wps rp7frege wph wps wch wi wi wps wph wph wch
    wi rp8frege ax-mp $.

  $( Closed form of ~ syl with swapped antecedents. This proposition
     differs from ~ frege5 only in an unessential way.  Identical to ~ imim1 .

     Proposition 9 of [Frege1879] p. 35.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege9 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wps wch wph frege5 wps wch wi wph wps wi wph wch wi frege8 ax-mp $.

  $( Result commuting antecedents within an antecedent.

     Proposition 10 of [Frege1879] p. 36.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege10 $p |- ( ( ( ph -> ( ps -> ch ) ) -> th )
                -> ( ( ps -> ( ph -> ch ) ) -> th ) ) $=
    wps wph wch wi wi wph wps wch wi wi wi wph wps wch wi wi wth wi wps wph wch
    wi wi wth wi wi wps wph wch frege8 wps wph wch wi wi wph wps wch wi wi wth
    frege9 ax-mp $.

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja . Identical to ~ jarr .

     Proposition 11 of [Frege1879] p. 36.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege11 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    wps wph wps wi wi wph wps wi wch wi wps wch wi wi wps wph ax-1 wps wph wps
    wi wch frege9 ax-mp $.

  $( A closed form of ~ com23 .

     Proposition 12 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege12 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ph -> ( ch -> ( ps -> th ) ) ) ) $=

    wps wch wth wi wi wch wps wth wi wi wi wph wps wch wth wi wi wi wph wch wps
    wth wi wi wi wi wps wch wth frege8 wps wch wth wi wi wch wps wth wi wi wph
    frege5 ax-mp $.

  $( A closed form of ~ com3r .

     Proposition 13 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege13 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ch -> ( ph -> ( ps -> th ) ) ) ) $=
    wph wps wch wth wi wi wi wph wch wps wth wi wi wi wi wph wps wch wth wi wi
    wi wch wph wps wth wi wi wi wi wph wps wch wth frege12 wph wps wch wth wi
    wi wi wph wch wps wth wi frege12 ax-mp $.

  $( Closed form of a deduction based on ~ com3r .

     Proposition 14 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege14 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( ph -> ( th -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    wps wch wth wta wi wi wi wth wps wch wta wi wi wi wi wph wps wch wth wta wi
    wi wi wi wph wth wps wch wta wi wi wi wi wi wps wch wth wta frege13 wps wch
    wth wta wi wi wi wth wps wch wta wi wi wi wph frege5 ax-mp $.

  $( A closed form of ~ com4r .

     Proposition 15 of [Frege1879] p. 38.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege15 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    wph wps wch wth wta wi wi wi wi wph wth wps wch wta wi wi wi wi wi wph wps
    wch wth wta wi wi wi wi wth wph wps wch wta wi wi wi wi wi wph wps wch wth
    wta frege14 wph wps wch wth wta wi wi wi wi wph wth wps wch wta wi wi
    frege12 ax-mp $.

  $( A closed form of ~ com34 .

     Proposition 16 of [Frege1879] p. 38.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege16 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) ) $=
    wps wch wth wta wi wi wi wps wth wch wta wi wi wi wi wph wps wch wth wta wi
    wi wi wi wph wps wth wch wta wi wi wi wi wi wps wch wth wta frege12 wps wch
    wth wta wi wi wi wps wth wch wta wi wi wi wph frege5 ax-mp $.

  $( A closed form of ~ com3l .

     Proposition 17 of [Frege1879] p. 39.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege17 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ps -> ( ch -> ( ph -> th ) ) ) ) $=
    wph wps wch wth wi wi wi wps wph wch wth wi wi wi wi wph wps wch wth wi wi
    wi wps wch wph wth wi wi wi wi wph wps wch wth wi frege8 wph wps wch wth wi
    wi wi wps wph wch wth frege16 ax-mp $.

  $( Closed form of a syllogism followed by a swap of antecedents.

     Proposition 18 of [Frege1879] p. 39.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege18 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( th -> ph ) -> ( ps -> ( th -> ch ) ) ) ) $=
    wph wps wch wi wi wth wph wi wth wps wch wi wi wi wi wph wps wch wi wi wth
    wph wi wps wth wch wi wi wi wi wph wps wch wi wth frege5 wph wps wch wi wi
    wth wph wi wth wps wch frege16 ax-mp $.

  $( A closed form of ~ syl6 .

     Proposition 19 of [Frege1879] p. 39.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege19 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( ch -> th ) -> ( ph -> ( ps -> th ) ) ) ) $=
    wps wch wi wch wth wi wps wth wi wi wi wph wps wch wi wi wch wth wi wph wps
    wth wi wi wi wi wps wch wth frege9 wps wch wi wch wth wi wps wth wi wph
    frege18 ax-mp $.

  $( A closed form of ~ syl8 .

     Proposition 20 of [Frege1879] p. 40.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege20 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( th -> ta ) -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    wps wch wth wi wi wth wta wi wps wch wta wi wi wi wi wph wps wch wth wi wi
    wi wth wta wi wph wps wch wta wi wi wi wi wi wps wch wth wta frege19 wps
    wch wth wi wi wth wta wi wps wch wta wi wi wph frege18 ax-mp $.

  $( Replace antecedent in antecedent.

     Proposition 21 of [Frege1879] p. 40.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege21 $p |- ( ( ( ph -> ps ) -> ch )
                  -> ( ( ph -> th ) -> ( ( th -> ps ) -> ch ) ) )  $=
    wph wth wi wth wps wi wph wps wi wi wi wph wps wi wch wi wph wth wi wth wps
    wi wch wi wi wi wph wth wps frege9 wph wth wi wth wps wi wph wps wi wch
    frege19 ax-mp $.

  $( A closed form of ~ com45 .

     Proposition 22 of [Frege1879] p. 41.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege22 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )
                  -> ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) ) $=
    wps wch wth wta wet wi wi wi wi wps wch wta wth wet wi wi wi wi wi wph wps
    wch wth wta wet wi wi wi wi wi wph wps wch wta wth wet wi wi wi wi wi wi
    wps wch wth wta wet frege16 wps wch wth wta wet wi wi wi wi wps wch wta wth
    wet wi wi wi wi wph frege5 ax-mp $.

  $( Syllogism followed by rotation of three antecedents.

     Proposition 23 of [Frege1879] p. 42.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege23 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( ta -> ph )
                       -> ( ps -> ( ch -> ( ta -> th ) ) ) ) ) $=
    wph wps wch wth wi wi wi wta wph wi wps wta wch wth wi wi wi wi wi wph wps
    wch wth wi wi wi wta wph wi wps wch wta wth wi wi wi wi wi wph wps wch wth
    wi wta frege18 wph wps wch wth wi wi wi wta wph wi wps wta wch wth frege22
    ax-mp $.

  $( Closed form for ~ a1d .  Deduction introducing an embedded
     antecedent.  Identical to ~ frege24ALT which was proved without
     relying on ~ frege8 .

     Proposition 24 of [Frege1879] p. 42.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege24 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    wph wps wi wch wph wps wi wi wi wph wps wi wph wch wps wi wi wi wph wps wi
    wch ax-1 wph wps wi wch wph wps frege12 ax-mp $.

  $( Closed form for ~ a1dd .

     Proposition 25 of [Frege1879] p. 42.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege25 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    wps wch wi wps wth wch wi wi wi wph wps wch wi wi wph wps wth wch wi wi wi
    wi wps wch wth frege24 wps wch wi wps wth wch wi wi wph frege5 ax-mp $.

  $( Identical to ~ idd .

     Proposition 26 of [Frege1879] p. 42.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege26 $p |- ( ph -> ( ps -> ps ) ) $=
    wps wph wps wi wi wph wps wps wi wi wps wph ax-1 wps wph wps frege8 ax-mp
    $.

  $( Identical to ~ id .

     Proposition 27 of [Frege1879] p. 43.
     (Contributed by Richard Penner, 4-Oct-2019.) $)
  frege27 $p |- ( ph -> ph ) $=
    wph wps wph wi wi wph wph wi wph wps ax-1 wph wps wph wi wi wph frege26
    ax-mp $.

  $( Contraposition. Identical to ~ con3 .

     Theorem *2.16 of [WhiteheadRussell] p. 103.

     Axiom 28 of [Frege1879] p. 43.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege28 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    wph wps con3 $.

  $( Closed form of ~ con3d .

     Proposition 29 of [Frege1879] p. 43.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege29 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( -. ch -> -. ps ) ) ) $=
    wps wch wi wch wn wps wn wi wi wph wps wch wi wi wph wch wn wps wn wi wi wi
    wps wch frege28 wps wch wi wch wn wps wn wi wph frege5 ax-mp $.

  $( Commuted, closed form of ~ con3d .

     Proposition 30 of [Frege1879] p. 44.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege30 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( -. ch -> -. ph ) ) ) $=
    wps wph wch wi wi wps wch wn wph wn wi wi wi wph wps wch wi wi wps wch wn
    wph wn wi wi wi wps wph wch frege29 wps wph wch wps wch wn wph wn wi wi
    frege10 ax-mp $.

  $( Identical to ~ notnot2 .

     Axiom 31 of [Frege1879] p. 44.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege31 $p |- ( -. -. ph -> ph ) $=
    wph notnot2 $.

  $( Deduce ~ con1 from ~ con3 .

     Proposition 32 of [Frege1879] p. 44.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege32 $p |- ( ( ( -. ph -> ps ) -> ( -. ps -> -. -. ph ) )
                  -> ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) ) $=
    wph wn wn wph wi wph wn wps wi wps wn wph wn wn wi wi wph wn wps wi wps wn
    wph wi wi wi wph frege31 wph wn wn wph wph wn wps wi wps wn frege7 ax-mp $.

  $( Identical to ~ con1 .

     Proposition 33 of [Frege1879] p. 44.
     (Contributed by Richard Penner, 6-Oct-2019.) $)
  frege33 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    wph wn wps wi wps wn wph wn wn wi wi wph wn wps wi wps wn wph wi wi wph wn
    wps frege28 wph wps frege32 ax-mp $.

  $( Closed form of ~ con1d .

     Proposition 34 of [Frege1879] p. 45.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege34 $p |- ( ( ph -> ( -. ps -> ch ) ) -> ( ph -> ( -. ch -> ps ) ) ) $=
    wps wn wch wi wch wn wps wi wi wph wps wn wch wi wi wph wch wn wps wi wi wi
    wps wch frege33 wps wn wch wi wch wn wps wi wph frege5 ax-mp $.

  $( Commuted, closed form of ~ con1d .

     Proposition 35 of [Frege1879] p. 45.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege35 $p |- ( ( ph -> ( -. ps -> ch ) ) -> ( -. ch -> ( ph -> ps ) ) ) $=
    wph wps wn wch wi wi wph wch wn wps wi wi wi wph wps wn wch wi wi wch wn
    wph wps wi wi wi wph wps wch frege34 wph wps wn wch wi wi wph wch wn wps
    frege12 ax-mp $.

  $( Identical to ~ pm2.24 .

     Proposition 36 of [Frege1879] p. 45.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege36 $p |- ( ph -> ( -. ph -> ps ) ) $=
    wph wps wn wph wi wi wph wph wn wps wi wi wph wps wn ax-1 wph wps wph
    frege34 ax-mp $.

  $( Similar to a closed form of ~ orcs .

     Proposition 37 of [Frege1879] p. 46.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege37 $p |- ( ( ( -. ph -> ps ) -> ch ) -> ( ph -> ch ) ) $=
    wph wph wn wps wi wi wph wn wps wi wch wi wph wch wi wi wph wps frege36 wph
    wph wn wps wi wch frege9 ax-mp $.

  $( Identical to ~ pm2.21 .

     Proposition 38 of [Frege1879] p. 46.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege38 $p |- ( -. ph -> ( ph -> ps ) ) $=
    wph wph wn wps wi wi wph wn wph wps wi wi wph wps frege36 wph wph wn wps
    frege8 ax-mp $.

  $( Syllogism between ~ pm2.18 and ~ pm2.24 .

     Proposition 39 of [Frege1879] p. 46.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege39 $p |- ( ( -. ph -> ph ) -> ( -. ph -> ps ) ) $=
    wph wn wph wps wi wi wph wn wph wi wph wn wps wi wi wph wps frege38 wph wn
    wph wps ax-2 ax-mp $.

  $( Anything implies ~ pm2.18 .

     Proposition 40 of [Frege1879] p. 46.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege40 $p |- ( -. ph -> ( ( -. ps -> ps ) -> ps ) ) $=
    wps wn wps wi wps wn wph wi wi wph wn wps wn wps wi wps wi wi wps wph
    frege39 wps wn wps wi wps wph frege35 ax-mp $.

  $( Identical to ~ notnot1 .

     Axiom 41 of [Frege1879] p. 47.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege41 $p |- ( ph -> -. -. ph ) $=
    wph notnot1 $.

  $( Not not ~ id .

     Proposition 42 of [Frege1879] p. 47.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege42 $p |- -. -. ( ph -> ph ) $=
    wph wph wi wph wph wi wn wn wph frege27 wph wph wi frege41 ax-mp $.

  $( Identical to ~ pm2.18 .

     Proposition 43 of [Frege1879] p. 47.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege43 $p |- ( ( -. ph -> ph ) -> ph ) $=
    wph wph wi wn wn wph wn wph wi wph wi wph frege42 wph wph wi wn wph frege40
    ax-mp $.

  $( Similar to a commuted ~ pm2.62 .

     Proposition 44 of [Frege1879] p. 47.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege44 $p |- ( ( -. ph -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    wph wn wph wi wph wi wph wn wps wi wps wph wi wph wi wi wph frege43 wph wn
    wph wph wps frege21 ax-mp $.

  $( Deduce ~ pm2.6 from ~ con1 .

     Proposition 45 of [Frege1879] p. 47.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege45 $p |- ( ( ( -. ph -> ps ) -> ( -. ps -> ph ) )
                  -> ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) ) $=
    wps wn wph wi wph wps wi wps wi wi wph wn wps wi wps wn wph wi wi wph wn
    wps wi wph wps wi wps wi wi wi wps wph frege44 wps wn wph wi wph wps wi wps
    wi wph wn wps wi frege5 ax-mp $.

  $( Identical to ~ pm2.6 .

     Proposition 46 of [Frege1879] p. 48.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege46 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    wph wn wps wi wps wn wph wi wi wph wn wps wi wph wps wi wps wi wi wph wps
    frege33 wph wps frege45 ax-mp $.

  $( Deduce consequence follows from either path implied by a disjunction.

     Proposition 47 of [Frege1879] p. 48.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege47 $p |- ( ( -. ph -> ps )
                  -> ( ( ps -> ch ) -> ( ( ph -> ch ) -> ch ) ) ) $=
    wph wn wch wi wph wch wi wch wi wi wph wn wps wi wps wch wi wph wch wi wch
    wi wi wi wph wch frege46 wph wn wch wph wch wi wch wi wps frege21 ax-mp $.

  $( Closed form of syllogism with internal disjunction.

     Proposition 48 of [Frege1879] p. 49.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege48 $p |- ( ( ph -> ( -. ps -> ch ) )
                  -> ( ( ch -> th ) -> ( ( ps -> th ) -> ( ph -> th ) ) ) ) $=
    wps wn wch wi wch wth wi wps wth wi wth wi wi wi wph wps wn wch wi wi wch
    wth wi wps wth wi wph wth wi wi wi wi wps wch wth frege47 wps wn wch wi wch
    wth wi wps wth wi wth wph frege23 ax-mp $.

  $( Closed form of deduction with disjunction.

     Proposition 49 of [Frege1879] p. 49.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege49 $p |- ( ( -. ph -> ps )
                  -> ( ( ph -> ch ) -> ( ( ps -> ch ) -> ch ) ) ) $=
    wph wn wps wi wps wch wi wph wch wi wch wi wi wi wph wn wps wi wph wch wi
    wps wch wi wch wi wi wi wph wps wch frege47 wph wn wps wi wps wch wi wph
    wch wi wch frege12 ax-mp $.

  $( Closed form of ~ jaoi .

     Proposition 50 of [Frege1879] p. 49.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege50 $p |- ( ( ph -> ps )
                  -> ( ( ch -> ps ) -> ( ( -. ph -> ch ) -> ps ) ) ) $=
    wph wn wch wi wph wps wi wch wps wi wps wi wi wi wph wps wi wch wps wi wph
    wn wch wi wps wi wi wi wph wch wps frege49 wph wn wch wi wph wps wi wch wps
    wi wps frege17 ax-mp $.

  $( Compare with ~ jaod .

     Proposition 51 of [Frege1879] p. 50.
     (Contributed by Richard Penner, 5-Oct-2019.) $)
  frege51 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( th -> ch )
                       -> ( ph -> ( ( -. ps -> th ) -> ch ) ) ) ) $=
    wps wch wi wth wch wi wps wn wth wi wch wi wi wi wph wps wch wi wi wth wch
    wi wph wps wn wth wi wch wi wi wi wi wps wch wth frege50 wps wch wi wth wch
    wi wps wn wth wi wch wi wph frege18 ax-mp $.

  $( Identical to ~ dfsbcq .

     Part of Axiom 52 of [Frege1879] p. 50.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege52a $p |- ( A = B -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) $=
    wph vx cA cB dfsbcq $.

  $( Identical to ~ fveq2 .

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
