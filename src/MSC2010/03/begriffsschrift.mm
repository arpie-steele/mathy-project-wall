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

   Numbered propositions from [Frege1879] . ~ ax-frege1 , ~ ax-frege2 ,
   ~ ax-frege8 , ~ ax-frege28 , ~ ax-frege31 , ~ ax-frege41 , frege52 ( see
   ~ frege52b and ~ frege52c for translations), and
   frege54 ( see ~ frege54b and ~ frege54c for
   translations) are considered "core" or axioms. However, at least
   ~ ax-frege8 can be derived from ~ ax-frege1 and ~ ax-frege2 , see ~
   axfrege8 .

   ~ frege58b is a new principle.
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter II Implication
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The case in which ` ph ` is denied, ` ps ` is affirmed, and ` ph ` is
     affirmed is excluded.  This is evident since ` ph ` cannot at the same
     time be denied and affirmed.

     Axiom 1 of [Frege1879] p. 26.  Identical to ~ ax-1 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (New usage is discouraged.) $)
  ax-frege1 $a |- ( ph -> ( ps -> ph ) ) $.

  $( If a proposition ` ch ` is a neccessary consequence of two propostions
     ` ps ` and ` ph ` and on of those, ` ps ` , is in turn a necessary
     consequence of the other, ` ph ` , then the proposition ` ch ` is a
     necessary consequence of the latter one, ` ph ` , alone.

     Axiom 2 of [Frege1879] p. 26.  Identical to ~ ax-2 .

     (Contributed by Richard Penner, 1-Oct-2019.)
     (New usage is discouraged.) $)
  ax-frege2 $a |- ( ( ph -> ( ps -> ch ) )
                 -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

  $( Simplification of triple conjunction.  Compare with ~ simp2 .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp-simp2-frege $p |- ( ph -> ( ps -> ( ch -> ps ) ) ) $=
    ( wi ax-frege1 ax-mp ) BCBDDZAGDBCEGAEF $.

  $( More general statement than ~ frege3 .  Like ~ ax-frege2 , it is
     essentially a closed form of ~ mpd , however it has an extra antecedent.

     It would be more natural to prove from ~ a1i and ~ ax-frege2 in Metamath.
     (Contributed by Richard Penner, 1-Oct-2019.) $)
  rp-frege3g $p |- ( ph
                    -> ( ( ps -> ( ch -> th ) )
                         -> ( ( ps -> ch ) -> ( ps -> th ) ) ) ) $=
    ( wi ax-frege2 ax-frege1 ax-mp ) BCDEEBCEBDEEEZAIEBCDFIAGH $.

  $( Add antecedent to ~ ax-frege2 .  Special case of ~ rp-frege3g .

     Proposition 3 of [Frege1879] p. 29.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege3 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( ph -> ps ) )
                      -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
    ( wi ax-frege2 ax-frege1 ax-mp ) CABDZDCADCBDDDZHIDCABEIHFG $.

  $( Double-use of ~ ax-frege2 .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp-misc1-frege $p |- ( ( ( ph -> ( ps -> ch ) ) -> ( ph -> ps ) )
                     -> ( ( ph -> ( ps -> ch ) ) -> ( ph -> ch ) ) ) $=
    ( wi ax-frege2 ax-mp ) ABCDDZABDZACDZDDGHDGIDDABCEGHIEF $.

  $( Introducing an embedded antecedent.  Alternate proof for ~ frege24 .
     Closed form for ~ a1d .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp-frege24 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    ( wi rp-simp2-frege ax-frege2 ax-mp ) ABCBDZDDABDAHDDABCEABHFG $.

  $( Deduction relatied to distribution.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  rp-frege4g $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                        -> ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) ) $=
    ( wi rp-frege3g ax-frege2 ax-mp ) ABCDEEZBCEBDEEZEEAIEAJEEABCDFAIJGH $.

  $( Special case of closed form of ~ a2d .  Special case of ~ rp-frege4g .

     Proposition 4 of [Frege1879] p. 31.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege4 $p |- ( ( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) )
                 -> ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
    ( wi frege3 ax-frege2 ax-mp ) ABDZCHDZCADCBDDZDDHIDHJDDABCEHIJFG $.

  $( A closed form of ~ syl .  Identical to ~ imim2 .

     Theorem *2.05 of [WhiteheadRussell] p. 100.

     Proposition 5 of [Frege1879] p. 32.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege5 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi ax-frege1 frege4 ax-mp ) ABDZCHDDHCADCBDDDHCEABCFG $.

  $( Distribute antecedent and add another.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp-7frege $p |- ( ( ph -> ( ps -> ch ) )
              -> ( th -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) ) $=
    ( wi ax-frege2 rp-frege24 ax-mp ) ABCEEZABEACEEZEIDJEEABCFIJDGH $.

  $( Elimination of a nested antecedent of special form.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp-4frege $p |- ( ( ph -> ( ( ps -> ph ) -> ch ) ) -> ( ph -> ch ) ) $=
    ( wi rp-simp2-frege rp-misc1-frege ax-mp ) ABADZCDDZAHDDIACDDIABEAHCFG $.

  $( Elimination of a nested antecedent of special form.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp-6frege $p |- ( ph
                   -> ( ( ps -> ( ( ch -> ps ) -> th ) ) -> ( ps -> th ) ) ) $=
    ( wi rp-4frege ax-frege1 ax-mp ) BCBEDEEBDEEZAIEBCDFIAGH $.

  $( Eliminate antecedent when it is implied by previous antecedent.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp-8frege $p |- ( ( ph -> ( ps -> ( ( ch -> ps ) -> th ) ) )
                   -> ( ph -> ( ps -> th ) ) ) $=
    ( wi rp-6frege ax-frege2 ax-mp ) ABCBEDEEZBDEZEEAIEAJEEABCDFAIJGH $.

  $( Closed form for ~ a1dd .

     Alternate route to Proposition 25 of [Frege1879] p. 42.  (Contributed by
     Richard Penner, 4-Oct-2019.) $)
  rp-frege25 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wi rp-frege24 frege5 ax-mp ) BCEZBDCEEZEAIEAJEEBCDFIJAGH $.

  $( A closed form of ~ imim2d which is a deduction adding nested antecedents.

     Proposition 6 of [Frege1879] p. 33.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege6 $p |- ( ( ph -> ( ps -> ch ) )
                 -> ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) ) $=
    ( wi frege5 ax-mp ) BCEZDBEDCEEZEAHEAIEEBCDFHIAFG $.

  $( Swap antecedents.  Identical to ~ pm2.04 .

     Proof follows closely proof of ~ pm2.04 in
     ~ http://us.metamath.org/mmsolitaire/pmproofs.txt , but in the style of
     [Frege1879] .

     This demonstrates that Axiom 8 of [Frege1879] p. 35 is redundant.

     (Contributed by Richard Penner, 1-Oct-2019.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  axfrege8 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi rp-7frege rp-8frege ax-mp ) ABCDDZBABDACDZDDDHBIDDABCBEHBAIFG $.

  $( A closed form of ~ syl6 .  The first antecedent is used to replace the
     consequent of the second antecedent.

     Proposition 7 of [Frege1879] p. 34.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege7 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( th -> ph ) ) -> ( ch -> ( th -> ps ) ) ) ) $=
    ( wi frege5 frege6 ax-mp ) ABEZDAEZDBEZEEICJECKEEEABDFIJKCGH $.

  $( Swap antecedents.  Third axiom of [Frege1879] but identical to ~ pm2.04
     which can be proved from only ~ ax-mp , ~ ax-frege1 , and ~ ax-frege2 .

     (Redundant) Axiom 8 of [Frege1879] p. 35.

     (Contributed by Richard Penner, 1-Oct-2019.) $)
  ax-frege8 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $.

  $( Identical to ~ idd .

     Proposition 26 of [Frege1879] p. 42.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege26 $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi ax-frege1 ax-frege8 ax-mp ) BABCCABBCCBADBABEF $.

  $( Identical to ~ id .

     Proposition 27 of [Frege1879] p. 43.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege27 $p |- ( ph -> ph ) $=
    ( wps wi ax-frege1 frege26 ax-mp ) ABACCZAACABDGAEF $.

  $( Closed form of ~ syl with swapped antecedents.  This proposition differs
     from ~ frege5 only in an unessential way.  Identical to ~ imim1 .

     Proposition 9 of [Frege1879] p. 35.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege9 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi frege5 ax-frege8 ax-mp ) BCDZABDZACDZDDIHJDDBCAEHIJFG $.

  $( A closed form of ~ com23 .

     Proposition 12 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege12 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ph -> ( ch -> ( ps -> th ) ) ) ) $=
    ( wi ax-frege8 frege5 ax-mp ) BCDEEZCBDEEZEAIEAJEEBCDFIJAGH $.

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  Identical to ~ jarr .

     Proposition 11 of [Frege1879] p. 36.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege11 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi ax-frege1 frege9 ax-mp ) BABDZDHCDBCDDBAEBHCFG $.

  $( Closed form for ~ a1d .  Deduction introducing an embedded antecedent.
     Identical to ~ rp-frege24 which was proved without relying on
     ~ ax-frege8 .

     Proposition 24 of [Frege1879] p. 42.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege24 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    ( wi ax-frege1 frege12 ax-mp ) ABDZCHDDHACBDDDHCEHCABFG $.

  $( A closed form of ~ com34 .

     Proposition 16 of [Frege1879] p. 38.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege16 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege12 frege5 ax-mp ) BCDEFFFZBDCEFFFZFAJFAKFFBCDEGJKAHI $.

  $( Closed form for ~ a1dd .

     Proposition 25 of [Frege1879] p. 42.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege25 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wi frege24 frege5 ax-mp ) BCEZBDCEEZEAIEAJEEBCDFIJAGH $.

  $( Closed form of a syllogism followed by a swap of antecedents.

     Proposition 18 of [Frege1879] p. 39.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege18 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( th -> ph ) -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wi frege5 frege16 ax-mp ) ABCEZEZDAEZDIEEEJKBDCEEEEAIDFJKDBCGH $.

  $( A closed form of ~ com45 .

     Proposition 22 of [Frege1879] p. 41.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege22 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )
                  -> ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) ) $=
    ( wi frege16 frege5 ax-mp ) BCDEFGGGGZBCEDFGGGGZGAKGALGGBCDEFHKLAIJ $.

  $( Result commuting antecedents within an antecedent.

     Proposition 10 of [Frege1879] p. 36.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege10 $p |- ( ( ( ph -> ( ps -> ch ) ) -> th )
                -> ( ( ps -> ( ph -> ch ) ) -> th ) ) $=
    ( wi ax-frege8 frege9 ax-mp ) BACEEZABCEEZEJDEIDEEBACFIJDGH $.

  $( A closed form of ~ com3l .

     Proposition 17 of [Frege1879] p. 39.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege17 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ps -> ( ch -> ( ph -> th ) ) ) ) $=
    ( wi ax-frege8 frege16 ax-mp ) ABCDEZEEZBAIEEEJBCADEEEEABIFJBACDGH $.

  $( A closed form of ~ com3r .

     Proposition 13 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege13 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ch -> ( ph -> ( ps -> th ) ) ) ) $=
    ( wi frege12 ax-mp ) ABCDEEEZACBDEZEEEHCAIEEEABCDFHACIFG $.

  $( Closed form of a deduction based on ~ com3r .

     Proposition 14 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege14 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( ph -> ( th -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege13 frege5 ax-mp ) BCDEFFFZDBCEFFFZFAJFAKFFBCDEGJKAHI $.

  $( A closed form of ~ syl6 .

     Proposition 19 of [Frege1879] p. 39.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege19 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( ch -> th ) -> ( ph -> ( ps -> th ) ) ) ) $=
    ( wi frege9 frege18 ax-mp ) BCEZCDEZBDEZEEAIEJAKEEEBCDFIJKAGH $.

  $( Syllogism followed by rotation of three antecedents.

     Proposition 23 of [Frege1879] p. 42.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege23 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( ta -> ph )
                       -> ( ps -> ( ch -> ( ta -> th ) ) ) ) ) $=
    ( wi frege18 frege22 ax-mp ) ABCDFZFFZEAFZBEJFFFFKLBCEDFFFFFABJEGKLBECDHI
    $.

  $( A closed form of ~ com4r .

     Proposition 15 of [Frege1879] p. 38.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege15 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege14 frege12 ax-mp ) ABCDEFFFFZADBCEFFZFFFJDAKFFFABCDEGJADKHI $.

  $( Replace antecedent in antecedent.

     Proposition 21 of [Frege1879] p. 40.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege21 $p |- ( ( ( ph -> ps ) -> ch )
                  -> ( ( ph -> th ) -> ( ( th -> ps ) -> ch ) ) ) $=
    ( wi frege9 frege19 ax-mp ) ADEZDBEZABEZEEKCEIJCEEEADBFIJKCGH $.

  $( A closed form of ~ syl8 .

     Proposition 20 of [Frege1879] p. 40.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege20 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( th -> ta ) -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege19 frege18 ax-mp ) BCDFFZDEFZBCEFFZFFAJFKALFFFBCDEGJKLAHI $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter II Implication and Negation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Contraposition.  Identical to ~ con3 .

     Theorem *2.16 of [WhiteheadRussell] p. 103.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  axfrege28 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( con3 ) ABC $.

  $( Contraposition.  Identical to ~ con3 .

     Theorem *2.16 of [WhiteheadRussell] p. 103.

     Axiom 28 of [Frege1879] p. 43.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  ax-frege28 $a |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $.

  $( Closed form of ~ con3d .

     Proposition 29 of [Frege1879] p. 43.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege29 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( -. ch -> -. ps ) ) ) $=
    ( wi wn ax-frege28 frege5 ax-mp ) BCDZCEBEDZDAIDAJDDBCFIJAGH $.

  $( Commuted, closed form of ~ con3d .

     Proposition 30 of [Frege1879] p. 44.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege30 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( -. ch -> -. ph ) ) ) $=
    ( wi wn frege29 frege10 ax-mp ) BACDDBCEAEDDZDABCDDIDBACFBACIGH $.

  $( Identical to ~ notnot2 .

     Axiom 31 of [Frege1879] p. 44.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  axfrege31 $p |- ( -. -. ph -> ph ) $=
    ( notnot2 ) AB $.

  $( Identical to ~ notnot2 .

     Axiom 31 of [Frege1879] p. 44.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  ax-frege31 $a |- ( -. -. ph -> ph ) $.

  $( Deduce ~ con1 from ~ con3 .

     Proposition 32 of [Frege1879] p. 44.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege32 $p |- ( ( ( -. ph -> ps ) -> ( -. ps -> -. -. ph ) )
                  -> ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) ) $=
    ( wn wi ax-frege31 frege7 ax-mp ) ACZCZADHBDZBCZIDDJKADDDAEIAJKFG $.

  $( Identical to ~ con1 .

     Proposition 33 of [Frege1879] p. 44.  (Contributed by Richard Penner,
     6-Oct-2019.) $)
  frege33 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    ( wn wi ax-frege28 frege32 ax-mp ) ACZBDZBCZHCDDIJADDHBEABFG $.

  $( Closed form of ~ con1d .

     Proposition 34 of [Frege1879] p. 45.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege34 $p |- ( ( ph -> ( -. ps -> ch ) ) -> ( ph -> ( -. ch -> ps ) ) ) $=
    ( wn wi frege33 frege5 ax-mp ) BDCEZCDBEZEAIEAJEEBCFIJAGH $.

  $( Commuted, closed form of ~ con1d .

     Proposition 35 of [Frege1879] p. 45.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege35 $p |- ( ( ph -> ( -. ps -> ch ) ) -> ( -. ch -> ( ph -> ps ) ) ) $=
    ( wn wi frege34 frege12 ax-mp ) ABDCEEZACDZBEEEIJABEEEABCFIAJBGH $.

  $( Identical to ~ pm2.24 .

     Proposition 36 of [Frege1879] p. 45.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege36 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi ax-frege1 frege34 ax-mp ) ABCZADDAACBDDAHEABAFG $.

  $( Similar to a closed form of ~ orcs .

     Proposition 37 of [Frege1879] p. 46.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege37 $p |- ( ( ( -. ph -> ps ) -> ch ) -> ( ph -> ch ) ) $=
    ( wn wi frege36 frege9 ax-mp ) AADBEZEICEACEEABFAICGH $.

  $( Identical to ~ pm2.21 .

     Proposition 38 of [Frege1879] p. 46.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege38 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn wi frege36 ax-frege8 ax-mp ) AACZBDDHABDDABEAHBFG $.

  $( Syllogism between ~ pm2.18 and ~ pm2.24 .

     Proposition 39 of [Frege1879] p. 46.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege39 $p |- ( ( -. ph -> ph ) -> ( -. ph -> ps ) ) $=
    ( wn wi frege38 ax-frege2 ax-mp ) ACZABDDHADHBDDABEHABFG $.

  $( Anything implies ~ pm2.18 .

     Proposition 40 of [Frege1879] p. 46.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege40 $p |- ( -. ph -> ( ( -. ps -> ps ) -> ps ) ) $=
    ( wn wi frege39 frege35 ax-mp ) BCZBDZHADDACIBDDBAEIBAFG $.

  $( Identical to ~ notnot1 .

     Axiom 41 of [Frege1879] p. 47.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  axfrege41 $p |- ( ph -> -. -. ph ) $=
    ( notnot1 ) AB $.

  $( Identical to ~ notnot1 .

     Axiom 41 of [Frege1879] p. 47.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  ax-frege41 $a |- ( ph -> -. -. ph ) $.

  $( Not not ~ id .

     Proposition 42 of [Frege1879] p. 47.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege42 $p |- -. -. ( ph -> ph ) $=
    ( wi wn frege27 ax-frege41 ax-mp ) AABZGCCADGEF $.

  $( Identical to ~ pm2.18 .

     Proposition 43 of [Frege1879] p. 47.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege43 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wi wn frege42 frege40 ax-mp ) AABCZCACABABADGAEF $.

  $( Similar to a commuted ~ pm2.62 .

     Proposition 44 of [Frege1879] p. 47.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege44 $p |- ( ( -. ph -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    ( wn wi frege43 frege21 ax-mp ) ACZADADHBDBADADDAEHAABFG $.

  $( Deduce ~ pm2.6 from ~ con1 .

     Proposition 45 of [Frege1879] p. 47.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege45 $p |- ( ( ( -. ph -> ps ) -> ( -. ps -> ph ) )
                  -> ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) ) $=
    ( wn wi frege44 frege5 ax-mp ) BCADZABDBDZDACBDZHDJIDDBAEHIJFG $.

  $( Identical to ~ pm2.6 .

     Proposition 46 of [Frege1879] p. 48.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege46 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wn wi frege33 frege45 ax-mp ) ACBDZBCADDHABDBDDABEABFG $.

  $( Deduce consequence follows from either path implied by a disjunction.

     Proposition 47 of [Frege1879] p. 48.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege47 $p |- ( ( -. ph -> ps )
                  -> ( ( ps -> ch ) -> ( ( ph -> ch ) -> ch ) ) ) $=
    ( wn wi frege46 frege21 ax-mp ) ADZCEACECEZEIBEBCEJEEACFICJBGH $.

  $( Closed form of syllogism with internal disjunction.

     Proposition 48 of [Frege1879] p. 49.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege48 $p |- ( ( ph -> ( -. ps -> ch ) )
                  -> ( ( ch -> th ) -> ( ( ps -> th ) -> ( ph -> th ) ) ) ) $=
    ( wn wi frege47 frege23 ax-mp ) BECFZCDFZBDFZDFFFAJFKLADFFFFBCDGJKLDAHI $.

  $( Closed form of deduction with disjunction.

     Proposition 49 of [Frege1879] p. 49.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege49 $p |- ( ( -. ph -> ps )
                  -> ( ( ph -> ch ) -> ( ( ps -> ch ) -> ch ) ) ) $=
    ( wn wi frege47 frege12 ax-mp ) ADBEZBCEZACEZCEEEIKJCEEEABCFIJKCGH $.

  $( Closed form of ~ jaoi .

     Proposition 50 of [Frege1879] p. 49.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege50 $p |- ( ( ph -> ps )
                  -> ( ( ch -> ps ) -> ( ( -. ph -> ch ) -> ps ) ) ) $=
    ( wn wi frege49 frege17 ax-mp ) ADCEZABEZCBEZBEEEJKIBEEEACBFIJKBGH $.

  $( Compare with ~ jaod .

     Proposition 51 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege51 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( th -> ch )
                       -> ( ph -> ( ( -. ps -> th ) -> ch ) ) ) ) $=
    ( wi wn frege50 frege18 ax-mp ) BCEZDCEZBFDECEZEEAJEKALEEEBCDGJKLAHI $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter II with logical equivalence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

 Here we leverage Benoit Jubin's ~ df-bj-if to partition a wff into
 two that are disjoint with the selector wff.

 Thus if we are given ` |- ( ph <-> if- ( ps , ch , th ) ) ` then
 we replace the concept (illegal in our notation ) ` ( ph `` ps ) `
 with ` if- ( ps , ch , th ) ` to reason about the values of the
 "function." Likewise, we replace the similarly illegal conept
 ` A. ps ph ` with ` ( ch /\ th ) ` .

$)
  $( PLEASE DESCRIBE ME. Identical to ~ bi1 .

     Part of Axiom 52 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     31-Oct-2019.) $)
  frege52aALT $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( bi1 ) ABC $.

  $( PLEASE DESCRIBE ME.

     Part of Axiom 52 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     29-Oct-2019.) $)
  bj-frege52a $p |- ( ( ph <-> ps ) -> ( if- ( ph , th , ch )
                                        -> if- ( ps , th , ch ) ) ) $=
    ( wif wi wn wa wb df-bj-if biimpi bi2 imim1d bi1 con3 anim12d biimpri syl56
    syl ) ADCEZADFZAGZCFZHZABIZBDFZBGZCFZHZBDCEZTUDADCJKUEUAUFUCUHUEBADABLMUEUG
    UBCUEABFUGUBFABNABOSMPUJUIBDCJQR $.

  $( PLEASE PUT DESCRIPTION HERE.

     _Note:_ in the Bauer-Meenfelberg translation published in van Heijenoort's
     collection _From Frege to Goedel_, this proof has the minor clause and
     result swapped.

     Proposition 53 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     31-Oct-2019.) $)
  frege53aALT $p |- ( ph -> ( ( ph <-> ps ) -> ps ) ) $=
    ( wb wi frege52aALT ax-frege8 ax-mp ) ABCZABDDAHBDDABEHABFG $.

  $( PLEASE PUT DESCRIPTION HERE.

     _Note:_ in the Bauer-Meenfelberg translation published in van Heijenoort's
     collection _From Frege to Goedel_, this proof has the minor clause and
     result swapped.

     Proposition 53 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     29-Oct-2019.) $)
  bj-frege53a $p |- ( if- ( ph , th , ch ) -> ( ( ph <-> ps )
                                               -> if- ( ps , th , ch ) ) ) $=
    ( wb wif wi bj-frege52a ax-frege8 ax-mp ) ABEZADCFZBDCFZGGLKMGGABCDHKLMIJ
    $.

  $( Reflexive equality of wffs.

     Part of Axiom 54 of [Frege1879] p. 50.  Identical to ~ biid .
     (Contributed by Richard Penner, 30-Oct-2019.) $)
  frege54a $p |- ( ph <-> ph ) $=
    ( biid ) AB $.

  $( Synonym for logical equivalence.  (Contributed by Richard Penner,
     30-Oct-2019.) $)
  bj-frege54cor0a $p |- ( ( ps <-> ph ) <-> if- ( ps , ph , -. ph ) ) $=
    ( wb wi wa wif dfbi2 ax-frege28 anim2i ax3h impbii df-bj-if bicomi 3bitri
    wn ) BACBADZABDZEZPBOAOZDZEZBASFZBAGRUAQTPABHITQPBAJIKUBUABASLMN $.

  $( Reflexive equality.  (Contributed by Richard Penner, 31-Oct-2019.) $)
  bj-frege54cor1a $p |- if- ( ph , ph , -. ph ) $=
    ( wb wn wif frege54a bj-frege54cor0a biimpi ax-mp ) AABZAAACDZAEIJAAFGH $.

  $( PLEASE PUT DESCRIPTION HERE.

     Core proof of Proposition 55 of [Frege1879] p. 50.  (Contributed by
     Richard Penner, 31-Oct-2019.) $)
  frege55aALT $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    ( wb bicom biimpi ) ABCBACABDE $.

  $( Necessary deduction regarding subsitution of value in equality.
     (Contributed by Richard Penner, 31-Oct-2019.) $)
  bj-frege55lem1a $p |- ( ( ta -> if- ( ps , ph , -. ph ) )
                              -> ( ta -> ( ps <-> ph ) ) ) $=
    ( wn wif wb wi bj-frege54cor0a biimpri a1i a2i ) CBAADEZBAFZLMGCMLABHIJK $.

  $( PLEASE PUT DESCRIPTION HERE.

     Core proof of Proposition 55 of [Frege1879] p. 50.  (Contributed by
     Richard Penner, 31-Oct-2019.) $)
  bj-frege55lem2a $p |- ( ( ph <-> ps )
                            -> if- ( ps , ph , -. ph ) ) $=
    ( wb wn wif wi bicom1 bj-frege54cor0a sylib idi ) ABCZBAADEZFKBACLABGABHIJ
    $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 55 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     31-Oct-2019.) $)
  bf-frege55a $p |- ( ( ph <-> ps ) -> if- ( ps , ph , -. ph ) ) $=
    ( wn wif wb wi bj-frege54cor1a bj-frege53a ax-mp ) AAACZDABEBAJDFAGABJAHI
    $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 55 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     31-Oct-2019.) $)
  bf-frege55cor1a $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    ( wb wn wif wi bf-frege55a bj-frege55lem1a ax-mp ) ABCZBAADEFJBACFABGABJHI
    $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 56 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     31-Oct-2019.) $)
  frege56aALT $p |- ( ( ( ph <-> ps ) -> ( ph -> ps ) )
                   -> ( ( ps <-> ph ) -> ( ph -> ps ) ) ) $=
    ( wb wi frege55aALT frege9 ax-mp ) BACZABCZDIABDZDHJDDBAEHIJFG $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 56 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     29-Oct-2019.) $)
  bj-frege56a $p |- ( ( ( ph <-> ps ) -> ( if- ( ph , ch , th )
                                              -> if- ( ps , ch , th ) ) )
                        -> ( ( ps <-> ph ) -> ( if- ( ph , ch , th )
                                                -> if- ( ps , ch , th ) ) )
                      ) $=
    ( wb wi wif bf-frege55cor1a frege9 ax-mp ) BAEZABEZFLACDGBCDGFZFKMFFBAHKLMI
    J $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 57 of [Frege1879] p. 51.  (Contributed by Richard Penner,
     31-Oct-2019.) $)
  frege57aALT $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    ( wb wi frege52aALT frege56aALT ax-mp ) BACBADZDABCHDBAEBAFG $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 57 of [Frege1879] p. 51.  (Contributed by Richard Penner,
     29-Oct-2019.) $)
  bj-frege57a $p |- ( ( ph <-> ps ) -> ( if- ( ps , ch , th )
                                           -> if- ( ph , ch , th ) ) ) $=
    ( wb wif wi bj-frege52a bj-frege56a ax-mp ) BAEBCDFACDFGZGABEKGBADCHBACDIJ
    $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter II with equivalence of sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( PLEASE DESCRIBE ME.

     Part of Axiom 52 of [Frege1879] p. 50.

     (Contributed by Richard Penner, 8-Oct-2019.) $)
  frege52b $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    ( weq wsb sbequ biimpd ) BCEADBFADCFABCDGH $.

  $( PLEASE PUT DESCRIPTION HERE.

     _Note:_ in the Bauer-Meenfelberg translation published in van Heijenoort's
     collection _From Frege to Goedel_, this proof has the minor clause and
     result swapped.

     Proposition 53 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     8-Oct-2019.) $)
  frege53b $p |- ( [ x / y ] ph -> ( x = z -> [ z / y ] ph ) ) $=
    ( weq wsb wi frege52b ax-frege8 ax-mp ) BDEZACBFZACDFZGGLKMGGABDCHKLMIJ $.

  $( Reflexive equality of sets.

     Part of Axiom 54 of [Frege1879] p. 50.  Slightly specialized ~ eqid .

     (Contributed by Richard Penner, 8-Oct-2019.) $)
  frege54b $p |- x = x $=
    ( cv eqid ) ABC $.

  $( Reflexive equality.

     (Contributed by Richard Penner, 9-Oct-2019.) $)
  frege54cor1b $p |- [ x / y ] y = x $=
    ( equsb1 ) BAC $.

  ${
    $d y z $.
    $( Necessary deduction regarding subsitution of value in equality.

       (Contributed by Richard Penner, 8-Oct-2019.) $)
    frege55lem1b $p |- ( ( ph -> [ x / y ] y = z )
                       -> ( ph -> x = z ) ) $=
      ( weq wsb wi cv eqsb3 biimpi a1i a2i ) ACDECBFZBDEZMNGAMNBCDHIJKL $.
  $}

  $( PLEASE PUT DESCRIPTION HERE.

     Core proof of Proposition 55 of [Frege1879] p. 50.  (Contributed by
     Richard Penner, 9-Oct-2019.) $)
  frege55lem2b $p |- ( x = y -> [ y / z ] z = x ) $=
    ( weq wsb wi frege54cor1b frege53b ax-mp ) CADZCAEABDJCBEFACGJACBHI $.

  ${
    $d x z $.  $d y z $.
    $( PLEASE PUT DESCRIPTION HERE.

       Note that ~ eqtr2 incorporates eqcom which is stronger than this
       proposition which is parallel to ~ equcom .  Is is possible that Frege
       tricked himself into assuming what he was out to prove?

       Proposition 55 of [Frege1879] p. 50.  (Contributed by Richard Penner,
       26-Oct-2019.) $)
    frege55b $p |- ( x = y -> y = x ) $=
      ( vz weq wsb frege55lem2b wi wa wex df-sb eqtr2 exlimiv adantl sylbi syl
      cv ) ABDCADZCBEZBADZABCFRCBDZQGZTQHZCIZHSQCBJUCSUAUBSCCPBPAPKLMNO $.
  $}

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 56 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     26-Oct-2019.) $)
  frege56b $p |- ( ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) )
                   -> ( y = x -> ( [ x / z ] ph -> [ y / z ] ph ) ) ) $=
    ( weq wi wsb frege55b frege9 ax-mp ) CBEZBCEZFLADBGADCGFZFKMFFCBHKLMIJ $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 57 of [Frege1879] p. 51.  (Contributed by Richard Penner,
     8-Oct-2019.) $)
  frege57b $p |- ( x = y -> ( [ y / z ] ph -> [ x / z ] ph ) ) $=
    ( weq wsb wi frege52b frege56b ax-mp ) CBEADCFADBFGZGBCEKGACBDHACBDIJ $.

  ${
    $d x y $.
    $( If ` A. x ph ` is affirmed, ` [ y / x ] ph ` cannot be denied.

       Identical to ~ bj-stdpc4v in Benoit Jubin's box.

       Axiom 58 of [Frege1879] p. 51.  (Contributed by Richard Penner,
       26-Oct-2019.) $)
    frege58b $p |- ( A. x ph -> [ y / x ] ph ) $=
      ( wal weq wi wsb ax-1 alimi wa wex sp ax6ev exintr mpi df-sb sylanbrc syl
      ) ABDBCEZAFZBDZABCGZATBASHIUATSAJBKZUBTBLUASBKUCBCMSABNOABCPQR $.
  $}

  ${
    $d x y $.
    $( Corollary.

       (Contributed by Richard Penner, 27-Oct-2019.) $)
    frege58bcor $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph
                                               -> [ y / x ] ps ) ) $=
      ( wi wal wsb frege58b sbim sylib ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.
  $}

  ${
    $d x y $.

    $( A kind of Aristotelian inference.

       _Note:_ in the Bauer-Meenfelberg translation published in van
       Heijenoort's collection _From Frege to Goedel_, this proof has the
       ~ frege12 incorrectly referenced.

       Proposition 59 of [Frege1879] p. 51.  (Contributed by Richard Penner,
       27-Oct-2019.) $)
    frege59b $p |- ( [ x / y ] ph
                   -> ( -. [ x / y ] ps -> -. A. y ( ph -> ps ) ) ) $=
      ( wi wal wsb wn frege58bcor frege30 ax-mp ) ABEDFZADCGZBDCGZEEMNHLHEEABDC
      ILMNJK $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 60 of [Frege1879] p. 52.  (Contributed by Richard Penner,
       27-Oct-2019.) $)
    frege60b $p |- ( A. x ( ph -> ( ps -> ch ) )
                     -> ( [ y / x ] ps
                          -> ( [ y / x ] ph -> [ y / x ] ch ) ) ) $=
      ( wi wal wsb frege58b sbim imbi2i bitri sylib frege12 ax-mp ) ABCFZFZDGZA
      DEHZBDEHZCDEHZFZFZFRTSUAFFFRQDEHZUCQDEIUDSPDEHZFUCAPDEJUEUBSBCDEJKLMRSTUA
      NO $.
  $}

  ${
    $d x y $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 61 of [Frege1879] p. 52.  (Contributed by Richard Penner,
       8-Oct-2019.) $)
    frege61b $p |- ( ( [ x / y ] ph -> ps ) -> ( A. y ph -> ps ) ) $=
      ( wal wsb wi frege58b frege9 ax-mp ) ADEZADCFZGLBGKBGGADCHKLBIJ $.
  $}

  ${
    $d x y $.
    $( A kind of Aristotelian inference.  This judgement replaces the mode of
       inference ~ barbara when the minor premise has a particular context.

       Proposition 62 of [Frege1879] p. 52.  (Contributed by Richard Penner,
       27-Oct-2019.) $)
    frege62b $p |- ( [ x / y ] ph
                     -> ( A. y ( ph -> ps ) -> [ x / y ] ps ) ) $=
      ( wi wal wsb frege58bcor ax-frege8 ax-mp ) ABEDFZADCGZBDCGZEELKMEEABDCHKL
      MIJ $.
  $}

  ${
    $d x y $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 63 of [Frege1879] p. 52.  (Contributed by Richard Penner,
       8-Oct-2019.) $)
    frege63b $p |- ( [ x / y ] ph
                   -> ( ps
                        -> ( A. y ( ph -> ch ) -> [ x / y ] ch ) ) ) $=
      ( wsb wi wal frege62b frege24 ax-mp ) AEDFZACGEHCEDFGZGLBMGGACDEILMBJK $.
  $}

  ${
    $d x y $.  $d y z $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 64 of [Frege1879] p. 53.  (Contributed by Richard Penner,
       27-Oct-2019.) $)
    frege64b $p |- ( ( [ x / y ] ph -> [ z / y ] ps )
                   -> ( A. y ( ps -> ch )
                        -> ( [ x / y ] ph -> [ z / y ] ch ) ) ) $=
      ( wsb wi wal frege62b frege18 ax-mp ) BEFGZBCHEIZCEFGZHHAEDGZMHNPOHHHBCFE
      JMNOPKL $.
  $}

  ${
    $d x y $.
    $( A kind of Aristotelian inference.  This judgement replaces the mode of
       inference ~ barbara when the minor premise has a general context.

       Proposition 65 of [Frege1879] p. 53.  (Contributed by Richard Penner,
       27-Oct-2019.) $)
    frege65b $p |- ( A. x ( ph -> ps )
                   -> ( A. x ( ps -> ch )
                        -> ( [ y / x ] ph -> [ y / x ] ch ) ) ) $=
      ( wi wsb wal sbim frege64b sylbi frege61b ax-mp ) ABFZDEGZBCFDHADEGZCDEGF
      FZFNDHQFOPBDEGFQABDEIABCEDEJKNQEDLM $.
  $}

  ${
    $d x y $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 66 of [Frege1879] p. 54.  (Contributed by Richard Penner,
       8-Oct-2019.) $)
    frege66b $p |- ( A. x ( ph -> ps )
                   -> ( A. x ( ch -> ph )
                        -> ( [ y / x ] ch -> [ y / x ] ps ) ) ) $=
      ( wi wal wsb frege65b ax-frege8 ax-mp ) CAFDGZABFDGZCDEHBDEHFZFFMLNFFCABD
      EILMNJK $.
  $}

  ${
    $d x y $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 67 of [Frege1879] p. 54.  (Contributed by Richard Penner,
       8-Oct-2019.) $)
    frege67b $p |- ( ( ( A. x ph <-> ps ) -> ( ps -> A. x ph ) )
                     -> ( ( A. x ph <-> ps ) -> ( ps -> [ y / x ] ph ) ) ) $=
      ( wal wsb wi wb frege58b frege7 ax-mp ) ACEZACDFZGLBHZBLGGNBMGGGACDILMNBJ
      K $.
  $}

  ${
    $d x y $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 68 of [Frege1879] p. 54.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege68b $p |- ( ( A. x ph <-> ps ) -> ( ps -> [ y / x ] ph ) ) $=
      ( wal wb wi wsb frege57aALT frege67b ax-mp ) ACEZBFZBLGGMBACDHGGLBIABCDJK
      $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
   _Begriffschift_ Chapter II with equivalence of classes (where they are sets)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( One side of ~ dfsbcq .

     Part of Axiom 52 of [Frege1879] p. 50.

     (Contributed by Richard Penner, 8-Oct-2019.) $)
  frege52c $p |- ( A = B -> ( [. A / x ]. ph -> [. B / x ]. ph ) ) $=
    ( wceq wsbc dfsbcq biimpd ) CDEABCFABDFABCDGH $.

  $( PLEASE PUT DESCRIPTION HERE.

     _Note:_ in the Bauer-Meenfelberg translation published in van Heijenoort's
     collection _From Frege to Goedel_, this proof has the minor clause and
     result swapped.

     Proposition 53 of [Frege1879] p. 50.  (Contributed by Richard Penner,
     8-Oct-2019.) $)
  frege53c $p |- ( [. A / x ]. ph -> ( A = B -> [. B / x ]. ph ) ) $=
    ( wceq wsbc wi frege52c ax-frege8 ax-mp ) CDEZABCFZABDFZGGLKMGGABCDHKLMIJ
    $.

  $( Reflexive equality of sets (as classes).

     Part of Axiom 54 of [Frege1879] p. 50.  Identical to ~ eqid .

     (Contributed by Richard Penner, 8-Oct-2019.) $)
  frege54c $p |- A = A $=
    ( eqid ) AB $.

  ${
    $d x A $.
    frege54c.1 $e |- A e. _V $.
    $( Reflexive equality.

       (Contributed by Richard Penner, 9-Oct-2019.) $)
    frege54cor1c $p |- [. A / x ]. x = A $=
      ( cv wceq cab wcel wsbc csn snid df-sn eleq2i biimpi ax-mp df-sbc biimpri
      ) BADBEZAFZGZQABHZBBIZGZSBCJUBSUARBABKLMNTSQABOPN $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Necessary deduction regarding subsitution of value in equality.

       (Contributed by Richard Penner, 16-Oct-2019.) $)
    frege55lem1c $p |- ( ( ph -> [. A / x ]. x = B )
                         -> ( ph -> A = B ) ) $=
      ( cv wceq wsbc cab wcel df-sbc wi wb ax-frege1 eqeq1 elab3g syl ibi sylbi
      imim2i ) BEZDFZBCGZCDFZAUBCUABHZIZUCUABCJUEUCUEUCUEKUEUCLUEUCMUAUCBCUDTCD
      NOPQRS $.
  $}

  ${
    $d x z $.
    $( PLEASE PUT DESCRIPTION HERE.

       Core proof of Proposition 55 of [Frege1879] p. 50.  (Contributed by
       Richard Penner, 9-Oct-2019.) $)
    frege55lem2c $p |- ( x = A -> [. A / z ]. z = x ) $=
      ( weq cv wsbc wceq wi vex frege54cor1c frege53c ax-mp ) BADZBAEZFNCGMBCFH
      BNAIJMBNCKL $.
  $}

  ${
    $d x y $.  $d A y $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 55 of [Frege1879] p. 50.  (Contributed by Richard Penner,
       2-Nov-2019.) $)
    frege55c $p |- ( x = A -> A = x ) $=
      ( vy cv wceq weq wsbc vex frege54cor1c frege53c ax-mp wex cab wcel df-sbc
      wi wa clelab bitri eqtr2 exlimiv sylbi syl ) ADZBEZCAFZCBGZBUDEZUFCUDGUEU
      GPCUDAHIUFCUDBJKUGCDZBEUFQZCLZUHUGBUFCMNUKUFCBOUFCBRSUJUHCUIBUDTUAUBUC $.
  $}

  ${
    $d x A $.  $d x B $.
    frege56c.b $e |- B e. C $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 56 of [Frege1879] p. 50.  (Contributed by Richard Penner,
       2-Nov-2019.) $)
    frege56c $p |- ( ( A = B -> ( [. A / x ]. ph -> [. B / x ]. ph ) )
                     -> ( B = A -> ( [. A / x ]. ph -> [. B / x ]. ph ) ) ) $=
      ( wceq wi wsbc cv elexi frege54cor1c frege53c ax-mp frege55lem1c frege9 )
      DCGZCDGZHZRABCIABDIHZHQTHHQBJDGZBCIHZSUABDIUBBDDEFKLUABDCMNQBCDONQRTPN $.
  $}

  ${
    $d x A $.  $d x B $.
    frege57c.a $e |- A e. C $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 57 of [Frege1879] p. 51.  (Contributed by Richard Penner,
       8-Oct-2019.) $)
    frege57c $p |- ( A = B -> ( [. B / x ]. ph -> [. A / x ]. ph ) ) $=
      ( wceq wsbc wi frege52c frege56c ax-mp ) DCGABDHABCHIZICDGMIABDCJABDCEFKL
      $.
  $}

  ${
    frege58c.a $e |- A e. B $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 58 of [Frege1879] p. 51.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege58newc $p |- ( A. x ph -> [. A / x ]. ph ) $=
      ( wal cab wcel wsbc wi spsbc ax-mp df-sbc biimpi syl biimpri ) ABFZCABGHZ
      ABCIZQSRCDHQSJEABCDKLSRABCMZNOSRTPO $.

    $( A kind of Aristotelian inference.

       Proposition 59 of [Frege1879] p. 51.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege59newc $p |- ( [. A / x ]. ph
                   -> ( -. [. A / x ]. ps -> -. A. x ( ph -> ps ) ) ) $=
      ( wi wal wsbc wn frege58newc sbcim1 syl frege30 ax-mp ) ABGZCHZACDIZBCDIZ
      GZGRSJQJGGQPCDITPCDEFKABCDLMQRSNO $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 60 of [Frege1879] p. 52.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege60newc $p |- ( A. x ( ph -> ( ps -> ch ) )
                   -> ( [. A / x ]. ps
                        -> ( [. A / x ]. ph -> [. A / x ]. ch ) ) ) $=
      ( wi wal wsbc frege58newc sbcim1 syl6 syl frege12 ax-mp ) ABCHZHZDIZADEJZ
      BDEJZCDEJZHZHZHSUATUBHHHSRDEJZUDRDEFGKUETQDEJUCAQDELBCDELMNSTUAUBOP $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 61 of [Frege1879] p. 52.  (Contributed by Richard Penner,
       8-Oct-2019.) $)
    frege61newc $p |- ( ( [. A / x ]. ph -> ps ) -> ( A. x ph -> ps ) ) $=
      ( wal wsbc wi frege58newc frege9 ax-mp ) ACGZACDHZINBIMBIIACDEFJMNBKL $.

    $( A kind of Aristotelian inference.  This judgement replaces the mode of
       inference ~ barbara when the minor premise has a particular context.

       Proposition 62 of [Frege1879] p. 52.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege62newc $p |- ( [. A / x ]. ph
                   -> ( A. x ( ph -> ps ) -> [. A / x ]. ps ) ) $=
      ( wi wal wsbc frege58newc sbcim1 syl ax-frege8 ax-mp ) ABGZCHZACDIZBCDIZG
      ZGQPRGGPOCDISOCDEFJABCDKLPQRMN $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 63 of [Frege1879] p. 52.  (Contributed by Richard Penner,
       8-Oct-2019.) $)
    frege63newc $p |- ( [. A / x ]. ph
                   -> ( ps
                        -> ( A. x ( ph -> ch ) -> [. A / x ]. ch ) ) ) $=
      ( wsbc wi wal frege62newc frege24 ax-mp ) ADEHZACIDJCDEHIZINBOIIACDEFGKNO
      BLM $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 64 of [Frege1879] p. 53.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege64newc $p |- ( ( [. C / x ]. ph -> [. A / x ]. ps )
                   -> ( A. x ( ps -> ch )
                        -> ( [. C / x ]. ph -> [. A / x ]. ch ) ) ) $=
      ( wsbc wi wal frege62newc frege18 ax-mp ) BDEIZBCJDKZCDEIZJJADGIZOJPRQJJJ
      BCDEFHLOPQRMN $.

    $( A kind of Aristotelian inference.  This judgement replaces the mode of
       inference ~ barbara when the minor premise has a general context.

       Proposition 65 of [Frege1879] p. 53.  (Contributed by Richard Penner,
       2-Nov-2019.) $)
    frege65newc $p |- ( A. x ( ph -> ps )
                   -> ( A. x ( ps -> ch )
                        -> ( [. A / x ]. ph -> [. A / x ]. ch ) ) ) $=
      ( wi wsbc wal sbcim1 frege64newc syl frege61newc ax-mp ) ABHZDEIZBCHDJADE
      IZCDEIHHZHPDJSHQRBDEIHSABDEKABCDEFEGLMPSDEFGNO $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 66 of [Frege1879] p. 54.  (Contributed by Richard Penner,
       8-Oct-2019.) $)
    frege66newc $p |- ( A. x ( ph -> ps )
                 -> ( A. x ( ch -> ph )
                      -> ( [. A / x ]. ch -> [. A / x ]. ps ) ) ) $=
      ( wi wal wsbc frege65newc ax-frege8 ax-mp ) CAHDIZABHDIZCDEJBDEJHZHHONPHH
      CABDEFGKNOPLM $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 67 of [Frege1879] p. 54.  (Contributed by Richard Penner,
       8-Oct-2019.) $)
    frege67c $p |- ( ( ( A. x ph <-> ps ) -> ( ps -> A. x ph ) )
                   -> ( ( A. x ph <-> ps ) -> ( ps -> [. A / x ]. ph ) ) ) $=
      ( wal wsbc wi wb frege58newc frege7 ax-mp ) ACGZACDHZINBJZBNIIPBOIIIACDEF
      KNOPBLM $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 68 of [Frege1879] p. 54.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege68c $p |- ( ( A. x ph <-> ps ) -> ( ps -> [. A / x ]. ph ) ) $=
      ( wal wb wi wsbc frege57aALT frege67c ax-mp ) ACGZBHZBNIIOBACDJIINBKABCDE
      FLM $.

  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter III Properties hereditary in a sequence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

   ` ( R " A ) C_ A ` means membership in ` A ` is hereditary in the
   sequence dictated by relation ` R ` .

$)

  ${
    $d x y z A $.  $d x y z R $.
    $( PLEASE PUT DESCRIPTION HERE.

       Definition 69 of [Frege1879] p. 55.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege69c $p |- ( A. x ( x e. A -> A. y ( x R y -> y e. A ) )
                  <-> ( R " A ) C_ A ) $=
      ( vz cv wcel wbr wi wal wex cima wss 19.21v bicomi albii alcom bitri cop
      wa impexp 19.23v 3bitri cab dfss2 vex weq opeq2 eleq1d wb df-br a1i bitrd
      anbi2d exbidv elab imbi1i dfima3 eqcomi sseq1i ) AFZCGZVABFZDHZVCCGZIZBJI
      ZAJZVBVDTZAKZVEIZBJZDCLZCMZVHVBVFIZBJZAJVOAJZBJVLVGVPAVPVGVBVFBNOPVOABQVQ
      VKBVQVIVEIZAJVKVOVRAVRVOVBVDVEUAOPVIVEAUBRPUCVLVBVAEFZSZDGZTZAKZEUDZCMZVN
      WEVLWEVCWDGZVEIZBJVLBWDCUEWGVKBWFVJVEWCVJEVCBUFEBUGZWBVIAWHWAVDVBWHWAVAVC
      SZDGZVDWHVTWIDVSVCVAUHUIWJVDUJWHVDWJVAVCDUKOULUMUNUOUPUQPROWDVMCVMWDAEDCU
      RUSUTRR $.
  $}

  ${
    $d a b x y $.  $d a b c p R $.  $d a b c p A $.
    frege69.a $e |- A = { y | ph } $.
    frege69.r $e |- R = { <. x , y >. | ps } $.
    $( What Frege means when he stays the property ` ph ` is dictated by the
       relation ` ps ` can be stated more compactly: the ` R ` -image of ` A `
       is a subset of ` A ` .

       Definition 69 of [Frege1879] p. 55.  (Contributed by Richard Penner,
       29-Oct-2019.) $)
    frege69 $p |- ( A. b ( [ b / y ] ph -> A. a ( [ b / x ] [ a / y ] ps
                                                  -> [ a / y ] ph ) )
                    <-> ( R " A ) C_ A ) $=
      ( vp wsb wi wal cv wcel wa wex weq albii vc cop wss eleq2i df-clab bitr2i
      cima cab copab wceq excom opth equcom anbi12ci bitri anbi1i 2exbii elopab
      2sb5 3bitr4i sbcom2 3bitri bicomi imbi12i 19.21v alcom impexp 19.23v abid
      vex imbi1i dfss2 eleq1 eleq1d anbi12d cbvexvw anbi2d exbidv syl5bb cbvabv
      opeq1 opeq2 dfima3 eqcomi sseq1i ) ADHLZBDGLCHLZADGLZMZGNZMZHNHOZEPZWLGOZ
      UBZFPZWNEPZMZGNZMZHNZWMWPQZHRZWQMZGNZFEUGZEUCZWKWTHWFWMWJWSWMWLADUHZPWFEX
      HWLIUDAHDUEUFWIWRGWGWPWHWQWPWGWPWOBCDUIZPZBCHLDGLZWGFXIWOJUDWOCOZDOZUBUJZ
      BQZDRCRZDGSZCHSZQZBQZCRDRZXJXKXPXOCRDRYAXOCDUKXOXTDCXNXSBXNHCSZGDSZQXSWLW
      NXLXMHVJGVJULYBXRYCXQHCUMGDUMUNUOUPUQUOBCDWOURBDCGHUSUTBCHDGVAVBVCWQWNXHP
      WHEXHWNIUDAGDUEUFVDTVDTXAWMWRMZGNZHNYDHNZGNXEWTYEHYEWTWMWRGVEVCTYDHGVFYFX
      DGYFXBWQMZHNXDYDYGHYGYDWMWPWQVGVCTXBWQHVHUOTVBXEWNXCGUHZPZWQMZGNZKOZEPZYL
      UAOZUBZFPZQZKRZUAUHZEUCZXGXDYJGXCYIWQYIXCXCGVIVCVKTYTWNYSPZWQMZGNYKGYSEVL
      UUBYJGUUAYIWQYSYHWNYRXCUAGYRWMWLYNUBZFPZQZHRUAGSZXCYQUUEKHKHSZYMWMYPUUDYL
      WLEVMUUGYOUUCFYLWLYNWAVNVOVPUUFUUEXBHUUFUUDWPWMUUFUUCWOFYNWNWLWBVNVQVRVSV
      TUDVKTUFYSXFEXFYSKUAFEWCWDWEVBVB $.

  $}

  ${
    $d u v A $.  $d u v R $.  $d y A $.  $d y R $.  $d u x $.  $d x y v $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 70 of [Frege1879] p. 58.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege70 $p |- ( ( R " A ) C_ A -> ( x e. A -> A. y ( x R y -> y e. A ) ) ) $=
      ( vu vv cv wcel wbr wi wal cima wss wsb sbim nfv eleq1 sbie imbi12i bitri
      wb frege69c frege68b breq1 sbf sbalv weq breq2 imbi12d cbvalvw sylbb mp2b
      imim2i ) EGZCHZUNFGZDIZUPCHZJZFKZJZEKDCLCMZUAVBVAEANZJVBAGZCHZVDBGZDIZVFC
      HZJZBKZJZJEFCDUBVAVBEAUCVCVKVBVCUOEANZUTEANZJVKUOUTEAOVLVEVMVJUOVEEAVEEPU
      NVDCQRVMVDUPDIZURJZFKVJUSVOEAFUSEANUQEANZUREANZJVOUQUREAOVPVNVQURUQVNEAVN
      EPUNVDUPDUDRUREAUREPUESTUFVOVIFBFBUGVNVGURVHUPVFVDDUHUPVFCQUIUJTSUKUMUL
      $.
  $}


  ${
    $d z x $.  $d z A $.  $d z R $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 71 of [Frege1879] p. 59.  (Contributed by Richard Penner,
       29-Oct-2019.) $)
    frege71 $p |- ( ( A. z ( x R z -> z e. A ) -> ( x R y -> y e. A ) )
                  -> ( ( R " A ) C_ A
                       -> ( x e. A -> ( x R y -> y e. A ) ) ) ) $=
      ( cima wss cv wcel wbr wi wal frege70 frege19 ax-mp ) EDFDGZAHZDIZQCHZEJS
      DIKCLZKKTQBHZEJUADIKZKPRUBKKKACDEMPRTUBNO $.
  $}

  ${
    $d c A $.  $d c R $.  $d c x $.  $d c y $.
    $( If property ` A ` is hereditary in the ` R ` -sequence, if ` x ` has
       property ` A ` , and if ` y ` is a result of an application of the
       procedure ` R ` to ` x ` , then ` y ` has property ` A ` .

       Proposition 72 of [Frege1879] p. 59.  (Contributed by Richard Penner,
       29-Oct-2019.) $)
    frege72 $p |- ( ( R " A ) C_ A -> ( x e. A -> ( x R y -> y e. A ) ) ) $=
      ( vc cv wbr wcel wi wal cima wss wsbc cvv frege58newc sbcim1 ax-mp biimpi
      vex syl csb wb sbcbr2g weq wceq ax-gen nfcv csbieb breq2i biimpri sbcel1v
      id bitri imim12i frege71 ) AFZEFZDGZUQCHZIZEJZUPBFZDGZVBCHZIZIDCKCLUPCHVE
      IIVAUTEVBMZVEUTEVBNBSZOVFUREVBMZUSEVBMZIVEURUSEVBPVCVHVIVDVHVCVHUPEVBUQUA
      ZDGZVCVBNHVHVKUBVGEVBUPUQDNUCQVJVBUPDEBUDZVLIZEJZVJVBUEZVMEVLULUFVNVOEVBU
      QVBVGEVBUGUHRQUIUMUJVIVDEVBCUKRUNTTABECDUOQ $.
  $}

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 73 of [Frege1879] p. 59.  (Contributed by Richard Penner,
     11-Nov-2019.) $)
  frege73 $p |- ( ( ( R " A ) C_ A -> x e. A )
                  -> ( ( R " A ) C_ A -> ( x R y -> y e. A ) ) ) $=
    ( cima wss cv wcel wbr wi frege72 ax-frege2 ax-mp ) DCECFZAGZCHZOBGZDIQCHJZ
    JJNPJNRJJABCDKNPRLM $.

  $( If ` x ` has a property ` A ` that is hereditary in the ` R ` -sequence,
     then every result of a application of the procedure ` R ` to ` x ` has the
     property ` A ` .

     Proposition 74 of [Frege1879] p. 60.  (Contributed by Richard Penner,
     11-Nov-2019.) $)
  frege74 $p |- ( x e. A -> ( ( R " A ) C_ A -> ( x R y -> y e. A ) ) ) $=
    ( cima wss cv wcel wbr wi frege72 ax-frege8 ax-mp ) DCECFZAGZCHZOBGZDIQCHJZ
    JJPNRJJABCDKNPRLM $.

  ${
    $d x y A $.  $d x y R $.
    $( If from the proposition that ` x ` has property ` A ` , whatever ` x `
       may be, it can be inferred that every result of an application of the
       procedure ` R ` to ` x ` has property ` A ` , then property ` A ` is
       hereditary in the ` R ` -sequence.

       Proposition 75 of [Frege1879] p. 60.  (Contributed by Richard Penner,
       11-Nov-2019.) $)
    frege75 $p |- ( A. x ( x e. A -> A. y ( x R y -> y e. A ) )
                  -> ( R " A ) C_ A ) $=
      ( cv wcel wbr wi wal cima wss wb frege69c frege52aALT ax-mp ) AEZCFPBEZDG
      QCFHBIHAIZDCJCKZLRSHABCDMRSNO $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter III Following in a sequence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

    ` p F c ` means ` c ` follows ` p ` in the ` R ` -sequence.
$)

  ${
    frege76.f $e |- F = { <. p , c >. | c e. |^| { f | ( ( R " { p } ) C_ f
                                                          /\ ( R " f ) C_ f )
                                                  }
                         } $.
    ${
      $d c p f x $.  $d c p f y $.  $d c p f R $.  $d f g x $.  $d f g y $.
      $d f g R $.
      $( PLEASE PUT DESCRIPTION HERE.

         Definition 76 of [Frege1879] p. 60.  (Contributed by Richard Penner,
         11-Nov-2019.) $)
      frege76lem $p |- ( A. g ( ( R " g ) C_ g -> ( ( R " { x } ) C_ g
                                                  -> y e. g ) ) <-> x F y ) $=
        ( cv wcel csn cima wss wa cab cint wel wi bitri wbr cop copab wal df-br
        eleq2i vex weq nfv sneq imaeq2d sseq1d anbi1d abbid inteqd eleq2d eleq1
        opelopab elintab ancomst impexp imaeq2 id sseq12d elequ2 imbi12d syl5bb
        sseq2 cbvalv 3bitrri ) AJZBJZFUAVKVLUBZFKVMHJZCGJZLZMZDJZNZCVRMZVRNZOZD
        PZQZKZGHUCZKZCEJZMZWHNZCVKLZMZWHNZBERZSZSZEUDZVKVLFUEFWFVMIUFWGVLWLVRNZ
        WAOZDPZQZKZWQWEVNXAKXBGHVKVLAUGBUGZGAUHZWDXAVNXDWCWTXDWBWSDXDDUIXDVSWRW
        AXDVQWLVRXDVPWKCVOVKUJUKULUMUNUOUPVNVLXAUQURXBWSBDRZSZDUDWQWSDVLXCUSXFW
        PDEXFWAWRXESZSZDEUHZWPXFWAWROXESXHWRWAXEUTWAWRXEVATXIWAWJXGWOXIVTWIVRWH
        VRWHCVBXIVCVDXIWRWMXEWNVRWHWLVHDEBVEVFVFVGVITTVJ $.
    $}

    ${
      $d c p b f $.  $d c p e $.  $d c p R $.  $d f g R $.  $d f g e $.
      $d f a R $.  $d a b $.  $d b g $.
      $( If from the two propositions that every result of an application of
         the procedure ` R ` to ` b ` has property ` f ` and that property
         ` f ` is hereditary in the ` R ` -sequence, it can be inferred,
         whatever ` f ` may be, that ` e ` has property ` f ` , then we say
         ` e ` follows ` b ` in the ` R ` -sequence.

         Definition 76 of [Frege1879] p. 60.  (Contributed by Richard Penner,
         11-Nov-2019.) $)
      frege76 $p |- ( A. f ( ( R " f ) C_ f
                      -> ( A. a ( b R a -> a e. f ) -> e e. f ) )
                      <-> b F e ) $=
        ( vg cv cima wss wbr wel wi wal wcel vex bitr4i csn df-br elimasn albii
        cop imbi1i dfss2 imbi2i weq imaeq2 id sseq12d sseq2 eleq2 imbi12d bitri
        cbvalv frege76lem ) ACKZLZUSMZGKZFKZANZFCOZPZFQZBCOZPZPZCQZAJKZLZVLMZAV
        BUALZVLMZBJOZPZPZJQZVBBKZDNVKVAVOUSMZVHPZPZCQVTVJWDCVIWCVAVGWBVHVGVCVOR
        ZVEPZFQWBVFWFFVDWEVEVDVBVCUEARWEVBVCAUBAVBVCGSFSUCTUFUDFVOUSUGTUFUHUDWD
        VSCJCJUIZVAVNWCVRWGUTVMUSVLUSVLAUJWGUKULWGWBVPVHVQUSVLVOUMUSVLWAUNUOUOU
        QUPGBACJDEHIURUP $.
    $}

    ${
      frege77.a $e |- A e. C $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 77 of [Frege1879] p. 62. $)
      frege77new $p |- ( x F y -> ( ( R " A ) C_ A -> ( A. a ( b R a -> a e. A )
                                                 -> y e. A ) ) ) $=
        ( cv cima wss wcel wi csb ax-mp wbr wal frege76 frege68c sbcim1 wsbc wb
        sbcssg csbima12 wceq imaeq12d eqtri elexi nfcv id sseq12i bitri biimpri
        csbief imim12i syl imim2i ) ?ANBNZGUAZECOZCPZJNINZEUAVGCQRIUBVCCQRZRZRZ
        EBFGH?AKLUC??VJ?VDFCDMUD?VIVD??VIEFNZOZVKPZ?FCUEVFVMFCUFZ?VHVNVFVNFCVLS
        ZFCVKSZPZVFCDQVNVQUGMFCVLVKDUHTVOVEVPCVOFCESZVPOZVEFCVKEUI?VSVEUJ??VREV
        PC??UKTULFCVKCCDMUMFCUNVKCUJUOUSUPUQUR?UTVAVBVAT $.
    $}

    $( PLEASE PUT DESCRIPTION HERE. Might have to replace A with f.

       Proposition 77 of [Frege1879] p. 62. $)
    frege77 $p |- ( x F y -> ( ( R " A ) C_ A -> ( A. a ( b R a -> a e. A )
                                                 -> y e. A ) ) ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 78 of [Frege1879] p. 63.  (Contributed by Richard Penner,
       10-Nov-2019.) $)
    frege78 $p |- ( ( R " A ) C_ A -> ( A. a ( b R a -> a e. A )
                                      -> ( x F y -> y e. A ) ) ) $=
      ( cv wbr cima wss wcel wi wal frege77 frege17 ax-mp ) ALBLZFMZDCNCOZILHLZ
      DMUECPQHRZUBCPZQQQUDUFUCUGQQQABCDEFGHIJKSUCUDUFUGTUA $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 79 of [Frege1879] p. 63.  (Contributed by Richard Penner,
       10-Nov-2019.) $)
    frege79 $p |- ( ( ( R " A ) C_ A -> A. a ( b R a -> a e. A ) )
                  -> ( ( R " A ) C_ A -> ( x F y -> y e. A ) ) ) $=
      ( cima wss cv wbr wcel wi wal frege78 ax-frege2 ax-mp ) DCLCMZINHNZDOUCCP
      QHRZANBNZFOUECPQZQQUBUDQUBUFQQABCDEFGHIJKSUBUDUFTUA $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 80 of [Frege1879] p. 63.  (Contributed by Richard Penner,
       10-Nov-2019.) $)
    frege80 $p |- ( ( x e. A
                      -> ( ( R " A ) C_ A -> A. a ( x R a -> a e. A ) ) )
                  -> ( x e. A
                       -> ( ( R " A ) C_ A -> ( x F y -> y e. A ) ) ) ) $=
      ( cima wss cv wbr wcel wi wal frege79 frege5 ax-mp ) DCKCLZAMZHMZDNUCCOPH
      QPZUAUBBMZFNUECOPPZPUBCOZUDPUGUFPPABCDEFGHAIJRUDUFUGST $.

    ${
      $d x y $.  $d y A $.  $d y R $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 81 of [Frege1879] p. 63.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege81 $p |- ( x e. A -> ( ( R " A ) C_ A -> ( x F y -> y e. A ) ) ) $=
        ( cv wcel cima wss wbr wi wal wa nfv frege74 imp alrimi frege80 ax-mp
        ex ) AJZCKZDCLCMZUEBJZDNUHCKZOZBPZOOUFUGUEUHFNUIOOOUFUGUKUFUGQZUJBULBRU
        FUGUJABCDSTUAUDABCDEFGBHIUBUC $.
    $}

    ${
      $d y x $.  $d y A $.  $d y R $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 81 of [Frege1879] p. 63.  (Contributed by Richard Penner,
         11-Nov-2019.) $)
      frege81cor1 $p |- ( x e. A -> ( ( R " A ) C_ A
                                    -> A. y ( x F y -> y e. A ) ) ) $=
        ( cv wcel cima wss wbr wi wal wa nfv frege81 imp alrimi ex ) AJZCKZDCLC
        MZUCBJZFNUFCKOZBPUDUEQZUGBUHBRUDUEUGABCDEFGHISTUAUB $.
    $}

    ${
      $d y x $.  $d y A $.  $d y F $.  $d y R $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 81 of [Frege1879] p. 63.  (Contributed by Richard Penner,
         11-Nov-2019.) $)
      frege81cor2 $p |- ( x e. A -> ( ( R " A ) C_ A -> ( F " { x } ) C_ A ) ) $=
        ( vy cv wcel cima wss wbr wi wal vex bicomi bitri imbi2i csn cop imbi1i
        frege81cor1 dfss2 elimasn df-br albii biimpi ax-mp ) AJZBKZCBLBMZUKIJZE
        NZUNBKZOZIPZOZOZULUMEUKUALZBMZOZOZAIBCDEFGHUDUTVDUSVCULURVBUMVBURVBUNVA
        KZUPOZIPURIVABUEVFUQIVEUOUPVEUKUNUBEKZUOEUKUNAQIQUFUOVGUKUNEUGRSUCUHSRT
        TUIUJ $.
    $}

    ${
      $d x y $.  $d y A $.  $d y R $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 82 of [Frege1879] p. 64.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege82 $p |- ( ( ph -> x e. A )
                    -> ( ( R " A ) C_ A -> ( ph -> ( x F y -> y e. A ) ) ) ) $=
        ( cv wcel cima wss wbr wi frege81 frege18 ax-mp ) BKZDLZEDMDNZTCKZGOUCD
        LPZPPAUAPUBAUDPPPBCDEFGHIJQUAUBUDARS $.
    $}

    ${
      $d x y $.  $d y B $.  $d y C $.  $d y R $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 83 of [Frege1879] p. 65.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege83 $p |- ( ( R " ( B u. C ) ) C_ ( B u. C )
                    -> ( x e. B -> ( x F y -> y e. ( B u. C ) ) ) ) $=
        ( cv wcel cun wi cima wss wbr wn frege36 ax-mp elun df-or bitri biimpri
        wo imim2i frege82 ) AKZCLZUHCDMZLZNZEUJOUJPUIUHBKZGQUMUJLNNNUIUIRUHDLZN
        ZNULUIUNSUOUKUIUKUOUKUIUNUEUOUHCDUAUIUNUBUCUDUFTUIABUJEFGHIJUGT $.
    $}

    ${
      $d x y $.  $d y A $.  $d y R $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 84 of [Frege1879] p. 65.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege84 $p |- ( ( R " A ) C_ A -> ( x e. A -> ( x F y -> y e. A ) ) ) $=
        ( cv wcel cima wss wbr wi frege81 ax-frege8 ax-mp ) AJZCKZDCLCMZSBJZFNU
        BCKOZOOUATUCOOABCDEFGHIPTUAUCQR $.
    $}

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 85 of [Frege1879] p. 66.  (Contributed by Richard Penner,
       10-Nov-2019.) $)
    frege85 $p |- ( x F y -> ( A. z ( x R z -> z e. A )
                               -> ( ( R " A ) C_ A -> y e. A ) ) ) $=
      ( cv wbr cima wss wcel wi wal frege77 frege12 ax-mp ) AKZBKZGLZEDMDNZUACK
      ZELUEDOPCQZUBDOZPPPUCUFUDUGPPPABDEFGHCAIJRUCUDUFUGST $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 86 of [Frege1879] p. 66.  (Contributed by Richard Penner,
       10-Nov-2019.) $)
    frege86 $p |- ( ( ( ( R " A ) C_ A -> y e. A )
                      -> ( ( R " A ) C_ A -> ( y R z -> z e. A ) ) )
                    -> ( x F y -> ( A. w ( x R w -> w e. A )
                                    -> ( ( R " A ) C_ A
                                         -> ( y R z -> z e. A ) ) ) ) ) $=
      ( cv wbr wcel wi wal cima wss frege85 frege19 ax-mp ) ALZBLZHMZUBDLZFMUEE
      NODPZFEQERZUCENOZOOUHUGUCCLZFMUIENOOZOUDUFUJOOOABDEFGHIJKSUDUFUHUJTUA $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 87 of [Frege1879] p. 66.  (Contributed by Richard Penner,
       10-Nov-2019.) $)
    frege87 $p |- ( x F y -> ( A. w ( x R w -> w e. A )
                               -> ( ( R " A ) C_ A
                                    -> ( y R z -> z e. A ) ) ) ) $=
      ( cima wss cv wcel wi wbr wal frege73 frege86 ax-mp ) FELEMZBNZEOPUBUCCNZ
      FQUDEOPPZPANZUCHQUFDNZFQUGEOPDRUEPPBCEFSABCDEFGHIJKTUA $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 88 of [Frege1879] p. 67.  (Contributed by Richard Penner,
       10-Nov-2019.) $)
    frege88 $p |- ( y R z -> ( x F y
                               -> ( A. w ( x R w -> w e. A )
                                    -> ( ( R " A ) C_ A -> z e. A ) ) ) ) $=
      ( cv wbr wcel wi wal cima wss frege87 frege15 ax-mp ) ALZBLZHMZUBDLZFMUEE
      NODPZFEQERZUCCLZFMZUHENZOOOOUIUDUFUGUJOOOOABCDEFGHIJKSUDUFUGUIUJTUA $.

    ${
      $d c p f x $.  $d c p y $.  $d c p R $.  $d f w R $.  $d f w x $.
      $d f y $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 89 of [Frege1879] p. 68.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege89 $p |- ( A. f ( ( R " f ) C_ f -> ( A. w ( x R w -> w e. f )
                                               -> y e. f ) )
                    -> x F y ) $=
        ( cv cima wss wbr wel wi wal wb frege76 frege52aALT ax-mp ) DEJZKUALAJZ
        CJDMCENOCPBENOOEPZUBBJFMZQUCUDODBEFGCAHIRUCUDST $.
    $}

    ${
      $d c p f x $.  $d c p y $.  $d c p R $.  $d f w R $.  $d f w x $.
      $d f y $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 90 of [Frege1879] p. 68.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege90 $p |- ( ( ph
                      -> A. f ( ( R " f ) C_ f
                                -> ( A. w ( x R w -> w e. f ) -> y e. f ) ) )
                    -> ( ph -> x F y ) ) $=
        ( cv cima wss wbr wel wi wal frege89 frege5 ax-mp ) EFKZLUAMBKZDKENDFOP
        DQCFOPPFQZUBCKGNZPAUCPAUDPPBCDEFGHIJRUCUDAST $.
    $}

    ${
      $d f x $.  $d f y $.  $d f R $.  $d f w $.  $d w x $.  $d w y $.
      $d w R $.  $d c p x $.  $d c p y $.  $d c p R $.  $d c p f $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 91 of [Frege1879] p. 68.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege91 $p |- ( x R y -> x F y ) $=
        ( vw cv wbr cima wss wel wi wal wsb cvv ax-mp imim2i nfv wsbc csb sbsbc
        wcel wb vex sbcbr2g nfcv id csbief breq2i 3bitri biimpri frege63b elsb3
        weq biimpi 3syl alrimi frege90 ) AJZBJZCKZCDJZLVEMZVBIJZCKZIDNZOIPZBDNZ
        OZOZDPOVDVBVCEKOVDVMDVDDUAVDVHIBQZVFVJVIIBQZOZOVMVNVDVNVHIVCUBZVBIVCVGU
        CZCKZVDVHIBUDVCRUEVQVSUFBUGZIVCVBVGCRUHSVRVCVBCIVCVGVCVTIVCUIIBUQUJUKUL
        UMUNVHVFVIBIUOVPVLVFVOVKVJVOVKBIDUPURTTUSUTVDABICDEFGHVAS $.
    $}

    ${
      $d f x $.  $d f y $.  $d f R $.  $d w x $.  $d w y $.  $d w z $.
      $d w F $.  $d w R $.  $d c p x $.  $d c p y $.  $d c p R $.  $d c p f $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 92 of [Frege1879] p. 69.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege92 $p |- ( x = z -> ( x R y -> z F y ) ) $=
        ( vw cv wbr wi wsb weq nfv sbf breq1 sbie imim12i frege53b frege91 sbi2
        biimpi biimpri syl sbi1 3imtr3g imim2i mp2 ) AKZBKZDLZJKZULFLZMZJANZACO
        ZUPJCNZMZMUMUKULFLZMZURUMCKZULFLZMZMZUPAJCUAABDEFGHIUBVBUQUTVFVBUMJANZU
        OJANZMUQVGUMVAVHVGUMUMJAUMJPZQUDVHVAUOVAJAVAJPUNUKULFRSUETUMUOJAUCUFUSV
        EURUSUMJCNUOJCNUMVDUMUOJCUGUMJCVIQUOVDJCVDJPUNVCULFRSUHUITUJ $.
    $}

    ${
      $d c f p R $.  $d c f p x $.  $d c f p y $.  $d f z $.  $d R z $.
      $d x z $.
      $( PLEASE PUT DESCRIPTION HERE. Expected to need ~ frege60b but ran into
         incompatible distinct varible requirements.

         Proposition 93 of [Frege1879] p. 70.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege93 $p |- ( A. f ( A. z ( x R z -> z e. f )
                           -> ( ( R " f ) C_ f -> y e. f ) ) -> x F y ) $=
        ( cv wbr wel wi wal cima wss ax-frege8 alimi frege90 ax-mp ) AJZCJDKCEL
        MCNZDEJZOUCPZBELZMMZENZUDUBUEMMZENMUGUABJFKMUFUHEUBUDUEQRUGABCDEFGHIST
        $.
    $}

    ${
      $d c f p R $.  $d c f p x $.  $d c f p z $.  $d f R w $.  $d f x w $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 94 of [Frege1879] p. 70.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege94 $p |- ( ( y R z
                      -> ( x F y
                           -> A. f ( A. w ( x R w -> w e. f )
                                     -> ( ( R " f ) C_ f -> z e. f ) ) ) )
                    -> ( y R z -> ( x F y -> x F z ) ) ) $=
        ( cv wbr wel wi wal cima wss frege93 frege7 ax-mp ) AKZDKELDFMNDOEFKZPU
        BQCFMNNFOZUACKZGLZNBKZUDELZUAUFGLZUCNNUGUHUENNNACDEFGHIJRUCUEUGUHST $.
    $}

    ${
      $d x f $.  $d y f $.  $d z f $.  $d F f $.  $d c p R $.  $d c p x $.
      $d c p z $.  $d c p f $.  $d w x $.  $d w f R $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 95 of [Frege1879] p. 70.  (Contributed by Richard Penner,
         10-Nov-2019.) $)
      frege95 $p |- ( y R z -> ( x F y -> x F z ) ) $=
        ( vw cv wbr wel wi wal cima wss wa frege88 ax-mp imp ax-gen nfv frege94
        stdpc5 ex ) BKZCKZDLZAKZUGFLZUJJKDLJEMNJODEKZPULQCEMNNZEOZNNUIUKUJUHFLN
        NUIUKUNUIUKRZUMNZEOUOUNNUPEUIUKUMABCJULDEFGHISUAUBUOUMEUOEUCUETUFABCJDE
        FGHIUDT $.
    $}

    ${
      $d c p f R $.  $d c p f x $.  $d c p f z $.  $d f y $.  $d f F $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 96 of [Frege1879] p. 71.  (Contributed by Richard Penner,
         9-Nov-2019.) $)
      frege96 $p |- ( x F y -> ( y R z -> x F z ) ) $=
        ( cv wbr wi frege95 ax-frege8 ax-mp ) BJZCJZDKZAJZPFKZSQFKZLLTRUALLABCD
        EFGHIMRTUANO $.
    $}

    ${
      $d a b f $.  $d a b f x $.  $d a b f F $.  $d a b f R $.  $d c p R $.
      $d c p f $.  $d c p a $.  $d c p x $.

      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 97 of [Frege1879] p. 71.  (Contributed by Richard Penner,
         9-Nov-2019.) $)
      frege97 $p |- ( R " ( F " { x } ) ) C_ ( F " { x } ) $=
        ( vb va cv csn cima wcel wbr wi cop df-br vex elimasn bitr4i wal imbi2i
        wss frege75 frege96 3imtr3i alrimiv mpg ) HJZDAJZKLZMZUIIJZBNZUMUKMZOZI
        UAOBUKLUKUCHHIUKBUDULUPIUJUIDNZUNUJUMDNZOULUPAHIBCDEFGUEUQUJUIPDMULUJUI
        DQDUJUIARZHRSTURUOUNURUJUMPDMUOUJUMDQDUJUMUSIRSTUBUFUGUH $.
    $}

    ${
      $d f x $.  $d f F $.  $d f R $.  $d y z $.  $d x z $.  $d F z $.
      $d R z $.  $d c p R $.  $d c p f $.  $d c p x $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 98 of [Frege1879] p. 71.  (Contributed by Richard Penner,
         9-Nov-2019.) $)
      frege98 $p |- ( x F y -> ( y F z -> x F z ) ) $=
        ( cv csn cima wcel wbr wi cop vex elimasn df-br bitr4i wss ax-mp imbi2i
        frege97 frege84 3imtr3i ) BJZFAJZKLZMZUGCJZFNZUKUIMZOZUHUGFNZULUHUKFNZO
        DUILUIUAUJUNOADEFGHIUDBCUIDEFGHIUEUBUJUHUGPFMUOFUHUGAQZBQRUHUGFSTUMUPUL
        UMUHUKPFMUPFUHUKUQCQRUHUKFSTUCUF $.
    $}
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter III Member of sequence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

    ` p ( F u. _I ) c ` means ` c ` is a member of the ` R ` -seqeunce
    begining with ` p ` and ` p ` is a member of the  ` R ` -seqeunce
    ending with ` c ` .
$)
  $( PLEASE PUT DESCRIPTION HERE.

     Definition 99 of [Frege1879] p. 71.  (Contributed by Richard Penner,
     9-Nov-2019.) $)
  frege99 $p |- ( ( -. x F z -> z = x ) <-> x ( F u. _I ) z ) $=
    ( cv cid cun wbr wn weq wi cop wcel df-br elun bicomi vex ideq eqcom 3bitri
    wo orbi12i df-or bitri ) ADZBDZCEFZGZUDUECGZHBAIZJZUGUDUEKZUFLUKCLZUKELZTZU
    JUDUEUFMUKCENUNUHUITUJULUHUMUIUHULUDUECMOUMUDUEEGZABIUIUOUMUDUEEMOUDUEBPQUD
    UERSUAUHUIUBUCSO $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 100 of [Frege1879] p. 72.  (Contributed by Richard Penner,
     9-Nov-2019.) $)
  frege100 $p |- ( x ( F u. _I ) z -> ( -. x F z -> z = x ) ) $=
    ( cv wbr wn weq wi cid cun wb frege99 frege57aALT ax-mp ) ADZBDZCEFBAGHZOPC
    IJEZKRQHABCLQRMN $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 101 of [Frege1879] p. 72.  (Contributed by Richard Penner,
     9-Nov-2019.) $)
  frege101 $p |- ( ( z = x -> ( z R v -> x F v ) )
                     -> ( ( x F z -> ( z R v -> x F v ) )
                          -> ( x ( F u. _I ) z -> ( z R v -> x F v ) ) ) ) $=
    ( cv cid cun wbr wn weq wi frege100 frege48 ax-mp ) AFZBFZEGHIZPQEIZJBAKZLL
    TQCFZDIPUAEILZLSUBLRUBLLLABEMRSTUBNO $.

  ${
    frege99.f $e |- F = { <. p , c >. | c e. |^| { f | ( ( R " { p } ) C_ f
                                                          /\ ( R " f ) C_ f )
                                                  }
                         } $.
    ${
      $d f v $.  $d f x $.  $d f z $.  $d f F $.  $d f R $.  $d c p R $.
      $d c p f $.  $d c p v $.  $d c p x $.  $d c p z $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 102 of [Frege1879] p. 72.  (Contributed by Richard Penner,
         9-Nov-2019.) $)
      frege102 $p |- ( x ( F u. _I ) z -> ( z R v -> x F v ) ) $=
        ( weq cv wbr wi cid cun frege92 frege96 frege101 mp2 ) BAJBKZCKZDLAKZUA
        FLMZMUBTFLUCMUBTFNOLUCMBCADEFGHIPABCDEFGHIQABCDFRS $.
    $}

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 103 of [Frege1879] p. 73. $)
    frege103 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 104 of [Frege1879] p. 73. $)
    frege104 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 105 of [Frege1879] p. 73. $)
    frege105 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 106 of [Frege1879] p. 73. $)
    frege106 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 107 of [Frege1879] p. 74. $)
    frege107 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 108 of [Frege1879] p. 74. $)
    frege108 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 109 of [Frege1879] p. 74. $)
    frege109 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 110 of [Frege1879] p. 75. $)
    frege110 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 111 of [Frege1879] p. 75. $)
    frege111 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 112 of [Frege1879] p. 76. $)
    frege112 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 113 of [Frege1879] p. 76. $)
    frege113 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 114 of [Frege1879] p. 76. $)
    frege114 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter III Single-valued procedure
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  ` Fun ``' ``' R ` means the procedure ` R ` is single-valued.
$)

  ${
    $d a b c $.  $d a R $.  $d b R $.  $d c R $.
    $( PLEASE PUT DESCRIPTION HERE.

       Definition 115 of [Frege1879] p. 77.  (Contributed by Richard Penner,
       9-Nov-2019.) $)
    frege115 $p |- ( A. c A. b ( b R c -> A. a ( b R a -> a = c ) )
                   <-> Fun `' `' R ) $=
      ( cv wbr wi wal ccnv vex brcnv bitri imbi1i albii bicomi wrel wex wa nfcv
      alcom weq wfun imbi12i cop wcel wsb nfv 19.21 wo id biimprd com12 alrimiv
      breq2d olcd biimpd imp alimi ax-5 biidd equsalhw sylib jaoi impbii impexp
      a2i dfsb2 ancom nfcnv nfbr mo df-br exbii cvv cres relres cnvcnv2 biimpri
      releqi ax-mp biantrur dffun5 ) CEZDEZAFZWCBEZAFZBDUAZGZBHZGZCHZDHWCWDAIZI
      ZFZWCWFWNFZWHGZBHZGZCHZDHZWNUBZWLWTDWKWSCWSWKWOWEWRWJWOWDWCWMFWEWCWDWMCJZ
      DJZKWDWCAXDXCKLWQWIBWPWGWHWPWFWCWMFWGWCWFWMXCBJZKWFWCAXEXCKLMNUCONNXAWNPZ
      WCWFUDWNUEZWHGZBHZDQZCHZRZXBXAXKXLXAWSDHZCHXKWSDCTXMXJCXMWRDQZXJXMWPWPBDU
      FZRZWHGZDHBHZXNXMXQBHZDHXRWSXSDWSXOWPRZWHGZBHZXSWSXOWQGZBHZYBWSWOWQGZBHZY
      DYFWSWOWQBWOBUGUHOYEYCBWOXOWQWOWHWPRZWHWPGZBHZUIZXOWOYJWOYIYGWOYHBWHWOWPW
      HWPWOWHWFWDWCWNWHUJUNZUKULUMUOYGWOYIWHWPWOWHWPWOYKUPZUQYIWHWOGZBHWOYHYMBW
      HWPWOYLVFURWOWOBDWOBUSWHWOUTVAVBVCVDXOYJWPBDVGOLMNLYCYABYAYCXOWPWHVEONLYA
      XQBXTXPWHXOWPVHMNLNXQDBTLXNXRWPBDDWCWFWNDWCSDWMDADASVIVIDWFSVJVKOLWRXIDWQ
      XHBWPXGWHWCWFWNVLMNVMLNLXFXKAVNVOZPZXFAVNVPXFYOWNYNAVQVSVRVTWALXBXLCBDWNW
      BOLL $.
  $}

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 116 of [Frege1879] p. 77. $)
  frege116 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 117 of [Frege1879] p. 78. $)
  frege117 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 118 of [Frege1879] p. 78. $)
  frege118 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 119 of [Frege1879] p. 78. $)
  frege119 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 120 of [Frege1879] p. 78. $)
  frege120 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  ${
    frege121.f $e |- F = { <. p , c >. | c e. |^| { f | ( ( R " { p } ) C_ f
                                                          /\ ( R " f ) C_ f )
                                                  }
                         } $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 121 of [Frege1879] p. 79. $)
    frege121 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 122 of [Frege1879] p. 79. $)
    frege122 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 123 of [Frege1879] p. 79. $)
    frege123 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 124 of [Frege1879] p. 80. $)
    frege124 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 125 of [Frege1879] p. 81. $)
    frege125 $p |- ( ph -> -. ph ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 126 of [Frege1879] p. 81. $)
    frege126 $p |- ( Fun `' `' R
                     -> ( b R a
                          -> ( b e. ( { w | w F y }
                                      u. { w | y ( F u. _I ) w } )
                               -> a e. ( { w | w F y }
                                         u. { w | y ( F u. _I ) w } ) ) ) ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 127 of [Frege1879] p. 82.  (Contributed by Richard Penner,
       9-Nov-2019.) $)
    frege127 $p |- ( Fun `' `' R
                     -> ( b e. ( { w | w F y }
                                 u. { w | y ( F u. _I ) w } )
                           -> ( b R a
                                 -> a e. ( { w | w F y }
                                           u. { w | y ( F u. _I ) w } ) ) ) )
      $=
      ( ccnv wfun cv wbr cab cid cun wcel wi frege126 frege12 ax-mp ) CKKLZHMZG
      MZCNZUDBMZAMZENBOUHUGEPQNBOQZRZUEUIRZSSSUCUJUFUKSSSABCDEFGHIJTUCUFUJUKUAU
      B $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 128 of [Frege1879] p. 83.  (Contributed by Richard Penner,
       9-Nov-2019.) $)
    frege128 $p |- ( ( b e. { w | y ( F u. _I ) w }
                       -> ( b R a -> a e. ( { w | w F y }
                                            u. { w | y ( F u. _I ) w } ) ) )
                     -> ( Fun `' `' R
                          -> ( b e. ( { w | w F y }
                                      u. { w | y ( F u. _I ) w } )
                                -> ( b R a
                                      -> a e. ( { w | w F y }
                                                u. { w | y ( F u. _I ) w } ) )
     ) ) ) $=
      ( cv cun wbr cab wcel wi wn wo bicomi bitri ccnv wfun frege127 ax-mp elun
      cid frege51 df-or pm4.25 orbi2i orass notbii imbi1i 3bitri imbi2i biimpi
      ) HKZAKZBKZEUFLMBNZOZUQGKZCMVBUSUREMBNZUTLZOPZPZCUAUAUBZUQVDOZQZVAPZVEPZP
      ZPZVFVGVHVEPZPZPZVOVMABCDEFGHIJUCVGVHVEVAUGUDVMVPVLVOVFVKVNVGVJVHVEVHVJVH
      UQVCOZVARZVQQVAPZVJUQVCUTUEZVQVAUHZVSVRQZVAPZVJVSVRWCVRVSWASVRVRVARZWCVRV
      QVAVARZRZWDVAWEVQVAUIUJWDWFVQVAVAUKSTVRVAUHTTWBVIVAVRVHVHVRVTSULUMTUNSUMU
      OUOUPUD $.

    $( If the procedure ` R ` is single-valued and ` b ` belongs to the ` R `
       -sequence begining with ` y ` or precedes ` y ` in the ` R ` -sequence,
       then every result of an application of the procedure ` R ` to ` b `
       belongs to the ` R ` -sequence begining with ` y ` or precedes ` y ` in
       the ` R ` -sequence.

       Proposition 129 of [Frege1879] p. 83. $)
    frege129 $p |- ( Fun `' `' R
                     -> ( b e. ( { w | w F y } u. { w | y ( F u. _I ) w } )
                           -> ( b R a
                                 -> a e. ( { w | w F y }
                                           u. { w | y ( F u. _I ) w } ) ) ) )
      $=
      (  ) ? $.

    ${
      $d a b R $.  $d a w $.  $d a y $.  $d a F $.
      $( PLEASE DESCRIBE ME.


         (Contributed by Richard Penner, 9-Nov-2019.) $)
      frege129cor $p |- ( Fun `' `' R
                     -> A. b ( b e. ( { w | w F y }
                                      u. { w | y ( F u. _I ) w } )
                               -> A. a ( b R a
                                         -> a e. ( { w | w F y }
                                                   u. { w | y ( F u. _I ) w }
                                                 ) ) ) ) $=
        ( ccnv wfun cv wbr cab cid cun wcel wi alrimiv wal wa frege129 imp ex )
        CKKLZHMZBMZAMZENBOUIUHEPQNBOQZRZUGGMZCNULUJRSZGUAZSHUFUKUNUFUKUBUMGUFUK
        UMABCDEFGHIJUCUDTUET $.

      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 130 of [Frege1879] p. 84.  (Contributed by Richard Penner,
         9-Nov-2019.) $)
      frege130 $p |- ( ( A. b ( b e. ( { w | w F y }
                                       u. { w | y ( F u. _I ) w } )
                              -> A. a ( b R a
                                        -> a e. ( { w | w F y }
                                                  u. { w | y ( F u. _I ) w } )
                                      )
                            )
                       -> ( R " ( { w | w F y } u. { w | y ( F u. _I ) w } ) )
                          C_ ( { w | w F y } u. { w | y ( F u. _I ) w } ) )
                     -> ( Fun `' `' R
                          -> ( R " ( { w | w F y }
                                     u. { w | y ( F u. _I ) w } ) )
                             C_ ( { w | w F y }
                                  u. { w | y ( F u. _I ) w } ) ) ) $=
        ( ccnv wfun cv wbr cab cid cun wcel wi wal wss frege129cor frege9 ax-mp
        cima ) CKKLZHMZBMZAMZENBOUIUHEPQNBOQZRUGGMZCNUKUJRSGTSHTZSULCUJUEUJUAZS
        UFUMSSABCDEFGHIJUBUFULUMUCUD $.

      ${
        $d b w $.  $d b y $.  $d b F $.

        $( If the procedure ` R ` is single-valued, then the property of
           belonging to the ` R ` -sequence begining with ` y ` or preceeding
           ` y ` in the ` R ` -sequence is hereditary in the ` R ` -sequence.

           Proposition 131 of [Frege1879] p. 85.  (Contributed by Richard
           Penner, 9-Nov-2019.) $)
        frege131 $p |- ( Fun `' `' R
                     -> ( R " ( { w | w F y } u. { w | y ( F u. _I ) w } ) )
                        C_ ( { w | w F y } u. { w | y ( F u. _I ) w } ) ) $=
          ( vb va cv wbr cab cid cun wcel wi wal cima ccnv wss frege75 frege130
          wfun ax-mp ) IKZBKZAKZELBMUHUGENOLBMOZPUFJKZCLUJUIPQJRQIRCUISUIUAZQCT
          TUDUKQIJUICUBABCDEFJIGHUCUE $.
      $}
    $}

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 132 of [Frege1879] p. 86.  (Contributed by Richard Penner,
       9-Nov-2019.) $)
    frege132 $p |- ( ( ( R " ( { w | w F y } u. { w | y ( F u. _I ) w } ) )
                     C_ ( { w | w F y } u. { w | y ( F u. _I ) w } )
                     -> ( x F y -> ( x F z
                                     -> ( -. z F y
                                                -> y ( F u. _I ) z ) ) ) )
                     -> ( Fun `' `' R
                          -> ( x F y
                               -> ( x F z
                                    -> ( -. z F y
                                         -> y ( F u. _I ) z ) ) ) ) ) $=
      ( ccnv wfun cv wbr cab cid cun cima wss wi wn frege131 frege9 ax-mp ) EKK
      LZEDMZBMZGNDOUGUFGPQZNDOQZRUISZTUJAMZUGGNUKCMZGNULUGGNUAUGULUHNTTTZTUEUMT
      TBDEFGHIJUBUEUJUMUCUD $.

    ${
      $d w x $.  $d w y $.  $d w z $.  $d w F $.  $d x y $.  $d x z $.
      $d x F $.  $d y z $.  $d F z $.  $d R z $.
      $( If ` y ` and ` z ` both follow in the ` R ` -sequence determined by
         single-valued procedure ` R ` and ` y ` does not follow ` z ` then
         ` z ` belongs to the ` R ` -sequence begining with ` y ` .

         Proposition 133 of [Frege1879] p. 86.  (Contributed by Richard Penner,
         9-Nov-2019.) $)
      frege133 $p |- ( Fun `' `' R
                     -> ( x F y
                          -> ( x F z
                               -> ( -. z F y -> y ( F u. _I ) z ) ) ) ) $=
        ( vw cv wbr cab cun wn wi ccnv wcel bicomi bitri cid cima frege83 brab1
        wss wfun wo elun df-or notbii wsbc df-sbc cvv vex breq2 sbcie2g imbi12i
        wb ax-mp imbi2i biimpi syl frege132 ) DJKZBKZFLJMZVEVDFUANZLZJMZNZUBVJU
        EZAKZVEFLZVLCKZFLZVNVEFLZOZVEVNVGLZPZPZPZPDQQUFWAPVKVLVFRZVOVNVJRZPZPZW
        AACVFVIDEFGHIUCWEWAWBVMWDVTVMWBAJVEFUDSWCVSVOWCVNVFRZVNVIRZUGZVSVNVFVIU
        HWHWFOZWGPVSWFWGUIWIVQWGVRWFVPVPWFCJVEFUDSUJWGVHJVNUKZVRWJWGVHJVNULSVNU
        MRWJVRURCUNVHVEVLVGLVRJAVNUMVDVLVEVGUOVLVNVEVGUOUPUSTUQTTUTUQVAVBABCJDE
        FGHIVCUS $.
    $}
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
     Corollaries from proofs of _Begriffschift_
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    a2dspfrege.1 $e |- ( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) ) $.
    $( Deduction distributing an embedded antecedent.  Special case of ~ a2d .

       (Contributed by Richard Penner, 4-Oct-2019.) $)
    a2dspfrege $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
      ( wi frege4 ax-mp ) ABEZCHEEHCAECBEEEDABCFG $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
     Additional proofs in the style of _Begriffschift_
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $( Specialized form of ~ idd .

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  iddspfrege $p |- ( ( ph -> ps ) -> ( ph -> ph ) ) $=
    ( wi ax-frege1 ax-frege2 ax-mp ) ABACCABCAACCABDABAEF $.

  $( Simplify when consequent is also third antecedent.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  simprlfrege $p |- ( ph -> ( ps -> ( ch -> ( th -> ch ) ) ) ) $=
    ( wi rp-simp2-frege ax-frege1 ax-mp ) BCDCEEEZAIEBCDFIAGH $.

  $( Distribution with two unnecessary antecendents.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  misc3frege $p |- ( ph
                     -> ( ps
                          -> ( ( ch -> ( th -> ta ) )
                               -> ( ( ch -> th ) -> ( ch -> ta ) ) ) ) ) $=
    ( wi rp-frege3g ax-frege1 ax-mp ) BCDEFFCDFCEFFFFZAJFBCDEGJAHI $.

  ${
    a1dfrege.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.  Identical to ~ a1d .

       (Contributed by Richard Penner, 4-Oct-2019.) $)
    a1dfrege $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi rp-frege24 ax-mp ) ABEACBEEDABCFG $.
  $}

  $( Simplify when consequent is also the first antecedent.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  simp1frege $p |- ( ph -> ( ps -> ( ch -> ph ) ) ) $=
    ( wi ax-frege1 rp-frege24 ax-mp ) ACADZDABHDDACEAHBFG $.

  ${
    rp4fregei.1 $e |- ( ph -> ( ( ps -> ph ) -> ch ) ) $.
    $( More naturally proved in Metamath from ~ ax-frege1 and ~ mpd .

       (Contributed by RichardPenner, 5-Oct-2019.) $)
    rp4fregei $p |- ( ph -> ch ) $=
      ( wi rp-4frege ax-mp ) ABAECEEACEDABCFG $.
  $}
