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

   Numbered propositions from [Frege1879] . ~ frege1 , ~ frege2 ,
   ~ frege8 , ~ frege28 , ~ frege31 , ~ frege41 , frege52 ( see
   ~ frege52b and ~ frege52c for translations), and
   frege54 ( see ~ frege54b and ~ frege54c for
   translations) are considered "core" or axioms. However, at least
   ~ frege8 can be derived from ~ frege1 and ~ frege2 , see ~
   frege8ALT .

   ~ frege58b is a new principle.
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
    ( ax-1 ) ABC $.
  $( $j restatement 'frege1' of 'ax-1'; $)

  ${
    frege1just1.1 $e |- ph $.
    frege1just1.2 $e |- ps $.
    frege1just1.3 $e |- -. ch $.
    $( Partial justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just1 $p |- -. ( ph -> ( ps -> ch ) ) $=
      ( wi wn mth8 ax-mp ) BCGZHZAKGHZCHZLFBNLGEBCIJJALMGDAKIJJ $.
  $}

  ${
    frege1just2.1 $e |- ch $.
    $( Partial justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just2 $p |- ( ph -> ( ps -> ch ) ) $=
      ( wi a1i ) BCEACBDFF $.
  $}

  ${
    frege1just3.1 $e |- -. ps $.
    $( Partial justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just3 $p |- ( ph -> ( ps -> ch ) ) $=
      ( wi pm2.21i a1i ) BCEABCDFG $.
  $}

  ${
    frege1just4.1 $e |- -. ph $.
    $( Partial justification for ~ frege1 .

       (Contributed by Richard Penner, 1-Oct-2019.) $)
    frege1just4 $p |- ( ph -> ( ps -> ch ) ) $=
      ( wi pm2.21i ) ABCEDF $.
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
    ( ax-2 ) ABCD $.
  $( $j restatement 'frege2' of 'ax-2'; $)

  $( Add antecedent to ~ ax-2 .  Special case of ~ frege3gen .

     Proposition 3 of [Frege1879] p. 29.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege3 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( ph -> ps ) )
                      -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
    ( wi ax-2 ax-1 ax-mp ) CABDZDCADCBDDDZHIDCABEIHFG $.

  $( Special case of closed form of ~ a2d .

     Proposition 4 of [Frege1879] p. 31.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege4 $p |- ( ( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) )
                 -> ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
    ( wi frege3 ax-2 ax-mp ) ABDZCHDZCADCBDDZDDHIDHJDDABCEHIJFG $.

  $( A closed form of ~ syl .  Identical to ~ imim2 .

     Theorem *2.05 of [WhiteheadRussell] p. 100.

     Proposition 5 of [Frege1879] p. 32.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege5 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi ax-1 frege4 ax-mp ) ABDZCHDDHCADCBDDDHCEABCFG $.

  $( A closed form of ~ imim2d which is a deduction adding nested antecedents.

     Proposition 6 of [Frege1879] p. 33.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege6 $p |- ( ( ph -> ( ps -> ch ) )
                 -> ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) ) $=
    ( wi frege5 ax-mp ) BCEZDBEDCEEZEAHEAIEEBCDFHIAFG $.

  $( A closed form of ~ syl6 .  The first antecedent is used to replace the
     consequent of the second antecedent.

     Proposition 7 of [Frege1879] p. 34.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege7 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( th -> ph ) ) -> ( ch -> ( th -> ps ) ) ) ) $=
    ( wi frege5 frege6 ax-mp ) ABEZDAEZDBEZEEICJECKEEEABDFIJKCGH $.

  $( Swap antecedents.  Third axiom of [Frege1879] but identical to ~ pm2.04
     which can be proved from only ~ ax-mp , ~ ax-1 , and ~ ax-2 .

     (Redundant) Axiom 8 of [Frege1879] p. 35.

     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege8 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( pm2.04 ) ABCD $.

  $( Closed form of ~ syl with swapped antecedents.  This proposition differs
     from ~ frege5 only in an unessential way.  Identical to ~ imim1 .

     Proposition 9 of [Frege1879] p. 35.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege9 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi frege5 frege8 ax-mp ) BCDZABDZACDZDDIHJDDBCAEHIJFG $.

  $( Result commuting antecedents within an antecedent.

     Proposition 10 of [Frege1879] p. 36.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege10 $p |- ( ( ( ph -> ( ps -> ch ) ) -> th )
                -> ( ( ps -> ( ph -> ch ) ) -> th ) ) $=
    ( wi frege8 frege9 ax-mp ) BACEEZABCEEZEJDEIDEEBACFIJDGH $.

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  Identical to ~ jarr .

     Proposition 11 of [Frege1879] p. 36.

     (Contributed by Richard Penner, 1-Oct-2019.)
     (Proof modification is discouraged.) $)
  frege11 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi ax-1 frege9 ax-mp ) BABDZDHCDBCDDBAEBHCFG $.

  $( A closed form of ~ com23 .

     Proposition 12 of [Frege1879] p. 37.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege12 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ph -> ( ch -> ( ps -> th ) ) ) ) $=
    ( wi frege8 frege5 ax-mp ) BCDEEZCBDEEZEAIEAJEEBCDFIJAGH $.

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

  $( A closed form of ~ com4r .

     Proposition 15 of [Frege1879] p. 38.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege15 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege14 frege12 ax-mp ) ABCDEFFFFZADBCEFFZFFFJDAKFFFABCDEGJADKHI $.

  $( A closed form of ~ com34 .

     Proposition 16 of [Frege1879] p. 38.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege16 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege12 frege5 ax-mp ) BCDEFFFZBDCEFFFZFAJFAKFFBCDEGJKAHI $.

  $( A closed form of ~ com3l .

     Proposition 17 of [Frege1879] p. 39.  (Contributed by Richard Penner,
     3-Oct-2019.) $)
  frege17 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ps -> ( ch -> ( ph -> th ) ) ) ) $=
    ( wi frege8 frege16 ax-mp ) ABCDEZEEZBAIEEEJBCADEEEEABIFJBACDGH $.

  $( Closed form of a syllogism followed by a swap of antecedents.

     Proposition 18 of [Frege1879] p. 39.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege18 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( th -> ph ) -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wi frege5 frege16 ax-mp ) ABCEZEZDAEZDIEEEJKBDCEEEEAIDFJKDBCGH $.

  $( A closed form of ~ syl6 .

     Proposition 19 of [Frege1879] p. 39.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege19 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( ch -> th ) -> ( ph -> ( ps -> th ) ) ) ) $=
    ( wi frege9 frege18 ax-mp ) BCEZCDEZBDEZEEAIEJAKEEEBCDFIJKAGH $.

  $( A closed form of ~ syl8 .

     Proposition 20 of [Frege1879] p. 40.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege20 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( th -> ta ) -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege19 frege18 ax-mp ) BCDFFZDEFZBCEFFZFFAJFKALFFFBCDEGJKLAHI $.

  $( Replace antecedent in antecedent.

     Proposition 21 of [Frege1879] p. 40.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege21 $p |- ( ( ( ph -> ps ) -> ch )
                  -> ( ( ph -> th ) -> ( ( th -> ps ) -> ch ) ) ) $=
    ( wi frege9 frege19 ax-mp ) ADEZDBEZABEZEEKCEIJCEEEADBFIJKCGH $.

  $( A closed form of ~ com45 .

     Proposition 22 of [Frege1879] p. 41.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege22 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )
                  -> ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) ) $=
    ( wi frege16 frege5 ax-mp ) BCDEFGGGGZBCEDFGGGGZGAKGALGGBCDEFHKLAIJ $.

  $( Syllogism followed by rotation of three antecedents.

     Proposition 23 of [Frege1879] p. 42.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege23 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( ta -> ph )
                       -> ( ps -> ( ch -> ( ta -> th ) ) ) ) ) $=
    ( wi frege18 frege22 ax-mp ) ABCDFZFFZEAFZBEJFFFFKLBCEDFFFFFABJEGKLBECDHI
    $.

  $( Closed form for ~ a1d .  Deduction introducing an embedded antecedent.
     Identical to ~ frege24ALT which was proved without relying on ~ frege8 .

     Proposition 24 of [Frege1879] p. 42.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege24 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    ( wi ax-1 frege12 ax-mp ) ABDZCHDDHACBDDDHCEHCABFG $.

  $( Closed form for ~ a1dd .

     Proposition 25 of [Frege1879] p. 42.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege25 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wi frege24 frege5 ax-mp ) BCEZBDCEEZEAIEAJEEBCDFIJAGH $.

  $( Identical to ~ idd .

     Proposition 26 of [Frege1879] p. 42.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege26 $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi ax-1 frege8 ax-mp ) BABCCABBCCBADBABEF $.

  $( Identical to ~ id .

     Proposition 27 of [Frege1879] p. 43.  (Contributed by Richard Penner,
     4-Oct-2019.) $)
  frege27 $p |- ( ph -> ph ) $=
    ( wps wi ax-1 frege26 ax-mp ) ABACCZAACABDGAEF $.

  $( Contraposition.  Identical to ~ con3 .

     Theorem *2.16 of [WhiteheadRussell] p. 103.

     Axiom 28 of [Frege1879] p. 43.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege28 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( con3 ) ABC $.

  $( Closed form of ~ con3d .

     Proposition 29 of [Frege1879] p. 43.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege29 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( -. ch -> -. ps ) ) ) $=
    ( wi wn frege28 frege5 ax-mp ) BCDZCEBEDZDAIDAJDDBCFIJAGH $.

  $( Commuted, closed form of ~ con3d .

     Proposition 30 of [Frege1879] p. 44.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege30 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( -. ch -> -. ph ) ) ) $=
    ( wi wn frege29 frege10 ax-mp ) BACDDBCEAEDDZDABCDDIDBACFBACIGH $.

  $( Identical to ~ notnot2 .

     Axiom 31 of [Frege1879] p. 44.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege31 $p |- ( -. -. ph -> ph ) $=
    ( notnot2 ) AB $.

  $( Deduce ~ con1 from ~ con3 .

     Proposition 32 of [Frege1879] p. 44.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege32 $p |- ( ( ( -. ph -> ps ) -> ( -. ps -> -. -. ph ) )
                  -> ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) ) $=
    ( wn wi frege31 frege7 ax-mp ) ACZCZADHBDZBCZIDDJKADDDAEIAJKFG $.

  $( Identical to ~ con1 .

     Proposition 33 of [Frege1879] p. 44.  (Contributed by Richard Penner,
     6-Oct-2019.) $)
  frege33 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    ( wn wi frege28 frege32 ax-mp ) ACZBDZBCZHCDDIJADDHBEABFG $.

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
    ( wn wi ax-1 frege34 ax-mp ) ABCZADDAACBDDAHEABAFG $.

  $( Similar to a closed form of ~ orcs .

     Proposition 37 of [Frege1879] p. 46.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege37 $p |- ( ( ( -. ph -> ps ) -> ch ) -> ( ph -> ch ) ) $=
    ( wn wi frege36 frege9 ax-mp ) AADBEZEICEACEEABFAICGH $.

  $( Identical to ~ pm2.21 .

     Proposition 38 of [Frege1879] p. 46.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege38 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn wi frege36 frege8 ax-mp ) AACZBDDHABDDABEAHBFG $.

  $( Syllogism between ~ pm2.18 and ~ pm2.24 .

     Proposition 39 of [Frege1879] p. 46.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege39 $p |- ( ( -. ph -> ph ) -> ( -. ph -> ps ) ) $=
    ( wn wi frege38 ax-2 ax-mp ) ACZABDDHADHBDDABEHABFG $.

  $( Anything implies ~ pm2.18 .

     Proposition 40 of [Frege1879] p. 46.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege40 $p |- ( -. ph -> ( ( -. ps -> ps ) -> ps ) ) $=
    ( wn wi frege39 frege35 ax-mp ) BCZBDZHADDACIBDDBAEIBAFG $.

  $( Identical to ~ notnot1 .

     Axiom 41 of [Frege1879] p. 47.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege41 $p |- ( ph -> -. -. ph ) $=
    ( notnot1 ) AB $.

  $( Not not ~ id .

     Proposition 42 of [Frege1879] p. 47.  (Contributed by Richard Penner,
     5-Oct-2019.) $)
  frege42 $p |- -. -. ( ph -> ph ) $=
    ( wi wn frege27 frege41 ax-mp ) AABZGCCADGEF $.

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

  ${
    $d ph ch $.  $d ph th $.  $d ps ch $.  $d ps th $.
    $( PLEASE DESCRIBE ME.

       Part of Axiom 52 of [Frege1879] p. 50.  (Contributed by Richard Penner,
       29-Oct-2019.) $)
    bj-frege52a $p |- ( ( ph <-> ps ) -> ( if- ( ph , th , ch )
                                        -> if- ( ps , th , ch ) ) ) $=
      ( wif wi wn wa wb df-bj-if biimpi bi2 imim1d bi1 con3 syl anim12d biimpri
      syl56 ) ADCEZADFZAGZCFZHZABIZBDFZBGZCFZHZBDCEZTUDADCJKUEUAUFUCUHUEBADABLM
      UEUGUBCUEABFUGUBFABNABOPMQUJUIBDCJRS $.
    $( PLEASE DESCRIBE ME.

       Part of Axiom 52 of [Frege1879] p. 50. $)
    frege52acor1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
      (  ) ? $.

    $( PLEASE PUT DESCRIPTION HERE.

       _Note:_ in the Bauer-Meenfelberg translation published in van
       Heijenoort's collection _From Frege to Goedel_, this proof has the minor
       clause and result swapped.

       Proposition 53 of [Frege1879] p. 50.  (Contributed by Richard Penner,
       29-Oct-2019.) $)
    bj-frege53a $p |- ( if- ( ph , th , ch ) -> ( ( ph <-> ps )
                                               -> if- ( ps , th , ch ) ) ) $=
      ( wb wif wi bj-frege52a frege8 ax-mp ) ABEZADCFZBDCFZGGLKMGGABCDHKLMIJ $.

    $( PLEASE PUT DESCRIPTION HERE.

       _Note:_ in the Bauer-Meenfelberg translation published in van
       Heijenoort's collection _From Frege to Goedel_, this proof has the minor
       clause and result swapped.

       Proposition 53 of [Frege1879] p. 50. $)
    frege53acor1 $p |- ( ph -> ( ( ph <-> ps ) -> ps ) ) $=
      (  ) ? $.

    $( Reflexive equality of wffs.

       Part of Axiom 54 of [Frege1879] p. 50.  Slightly specialized ~ eqid . $)
    frege54a $p |- ( ph <-> ph ) $=
      (  ) ? $.

    $( Reflexive equality. $)
    bj-frege54cor1a $p |- ( if- ( ph , T. , F. ) <-> ph ) $=
      (  ) ? $.

    ${
      $( Necessary deduction regarding subsitution of value in equality. $)
      bj-frege55lem1a $p |- ( ( ta -> ( if- ( ph , T. , F. ) <-> ps ) )
                         -> ( ta -> ( ph <-> ps ) ) ) $=
        (  ) ? $.
    $}

    $( PLEASE PUT DESCRIPTION HERE.

       Core proof of Proposition 55 of [Frege1879] p. 50. $)
    bj-frege55lem2a $p |- ( ( ph <-> ps )
                            -> ( if- ( ps , T. , F. ) <-> ph ) ) $=
      (  ) ? $.

    ${
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 55 of [Frege1879] p. 50. $)
      frege55a $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
        (  ) ? $.
    $}

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 56 of [Frege1879] p. 50.  (Contributed by Richard Penner,
       29-Oct-2019.) $)
    bj-frege56a $p |- ( ( ( ph <-> ps ) -> ( if- ( ph , ch , th )
                                        -> if- ( ps , ch , th ) ) )
                   -> ( ( ps <-> ph ) -> ( if- ( ph , ch , th )
                                           -> if- ( ps , ch , th ) ) ) ) $=
      ( wb wi wif frege55a frege9 ax-mp ) BAEZABEZFLACDGBCDGFZFKMFFBAHKLMIJ $.

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 57 of [Frege1879] p. 51.  (Contributed by Richard Penner,
       29-Oct-2019.) $)
    bj-frege57a $p |- ( ( ph <-> ps ) -> ( if- ( ps , ch , th )
                                      -> if- ( ph , ch , th ) ) ) $=
      ( wb wif wi bj-frege52a bj-frege56a ax-mp ) BAEBCDFACDFGZGABEKGBADCHBACDI
      J $.
  $}

  $( PLEASE DESCRIBE ME.

     Part of Axiom 52 of [Frege1879] p. 50. $)
  frege52aALT $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     _Note:_ in the Bauer-Meenfelberg translation published in van Heijenoort's
     collection _From Frege to Goedel_, this proof has the minor clause and
     result swapped.

     Proposition 53 of [Frege1879] p. 50. $)
  frege53aALT $p |- ( ph -> ( ( ph <-> ps ) -> ps ) ) $=
    (  ) ? $.


  $( PLEASE PUT DESCRIPTION HERE.

     Core proof of Proposition 55 of [Frege1879] p. 50. $)
  frege55aALT $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    (  ) ? $.


  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 56 of [Frege1879] p. 50. $)
  frege56aALT $p |- ( ( ( ph <-> ps ) -> ( ph -> ps ) )
                   -> ( ( ps <-> ph ) -> ( ph -> ps ) ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 57 of [Frege1879] p. 51. $)
  frege57aALT $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    (  ) ? $.

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
    ( weq wsb wi frege52b frege8 ax-mp ) BDEZACBFZACDFZGGLKMGGABDCHKLMIJ $.

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
      ( wi wal wsb frege58bcor frege8 ax-mp ) ABEDFZADCGZBDCGZEELKMEEABDCHKLMIJ
      $.
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
      ( wi wal wsb frege65b frege8 ax-mp ) CAFDGZABFDGZCDEHBDEHFZFFMLNFFCABDEIL
      MNJK $.
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

       Proposition 68 of [Frege1879] p. 54. $)
    frege68b $p |- ( ( A. x ph <-> ps ) -> ( ps -> [ y / x ] ph ) ) $=
      (  ) ? $.
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
    ( wceq wsbc wi frege52c frege8 ax-mp ) CDEZABCFZABDFZGGLKMGGABCDHKLMIJ $.

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
    $d x A $.  $d x y $.
    $( Necessary deduction regarding subsitution of value in equality.

       (Contributed by Richard Penner, 16-Oct-2019.) $)
    frege55lem1c $p |- ( ( ph -> [. A / x ]. x = y )
                         -> ( ph -> A = y ) ) $=
      ( weq wsbc cv wceq cab wcel df-sbc wi wb ax-1 eqeq1 elab3g syl ibi imim2i
      sylbi ) BCEZBDFZDCGZHZAUBDUABIZJZUDUABDKUFUDUFUDUFLUFUDMUFUDNUAUDBDUEBGDU
      COPQRTS $.
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

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 55 of [Frege1879] p. 50. $)
  frege55c $p |- ( x = A -> A = x ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 56 of [Frege1879] p. 50. $)
  frege56c $p |- ( ( A = B -> ( [. A / x ]. ph -> [. B / x ]. ph ) )
                   -> ( B = A -> ( [. A / x ]. ph -> [. B / x ]. ph ) ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 57 of [Frege1879] p. 51.  (Contributed by Richard Penner,
     8-Oct-2019.) $)
  frege57c $p |- ( A = B -> ( [. B / x ]. ph -> [. A / x ]. ph ) ) $=
    ( wceq wsbc wi frege52c frege56c ax-mp ) DCEABDFABCFGZGCDEKGABDCHABDCIJ $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 58 of [Frege1879] p. 51. $)
  frege58c $p |- ( A. x ph -> [. A / x ]. ph ) $=
    (  ) ? $.

  $( A kind of Aristotelian inference.

     Proposition 59 of [Frege1879] p. 51. $)
  frege59c $p |- ( [. A / x ]. ph
                   -> ( -. [. A / x ]. ps -> -. A. x ( ph -> ps ) ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 60 of [Frege1879] p. 52. $)
  frege60c $p |- ( A. x ( ph -> ( ps -> ch ) )
                   -> ( [. A / x ]. ph
                        -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 61 of [Frege1879] p. 52.  (Contributed by Richard Penner,
     8-Oct-2019.) $)
  frege61c $p |- ( ( [. A / x ]. ph -> ps ) -> ( A. x ph -> ps ) ) $=
    ( wal wsbc wi frege58c frege9 ax-mp ) ACEZACDFZGLBGKBGGACDHKLBIJ $.

  $( A kind of Aristotelian inference.  This judgement replaces the mode of
     inference ~ barbara when the minor premise has a particular context.

     Proposition 62 of [Frege1879] p. 52. $)
  frege62c $p |- ( [. A / x ]. ph
                   -> ( A. x ( ph -> ps ) -> [. A / x ]. ps ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 63 of [Frege1879] p. 52.  (Contributed by Richard Penner,
     8-Oct-2019.) $)
  frege63c $p |- ( [. A / x ]. ph
                   -> ( ps
                        -> ( A. x ( ph -> ch ) -> [. A / x ]. ch ) ) ) $=
    ( wsbc wi wal frege62c frege24 ax-mp ) ADEFZACGDHCDEFGZGLBMGGACDEILMBJK $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 64 of [Frege1879] p. 53. $)
  frege64c $p |- ( ( [. A / x ]. ph -> [. B / x ]. ps )
                   -> ( A. x ( ps -> ch )
                        -> ( [. A / x ]. ph -> [. B / x ]. ch ) ) ) $=
    (  ) ? $.

  $( A kind of Aristotelian inference.  This judgement replaces the mode of
     inference ~ barbara when the minor premise has a general context.

     Proposition 65 of [Frege1879] p. 53. $)
  frege65c $p |- ( A. x ( ph -> ps )
                   -> ( A. x ( ps -> ch )
                        -> ( [. A / x ]. ph -> [. A / x ]. ch ) ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 66 of [Frege1879] p. 54.  (Contributed by Richard Penner,
     8-Oct-2019.) $)
  frege66c $p |- ( A. x ( ph -> ps )
                   -> ( A. x ( ch -> ph )
                        -> ( [. A / x ]. ch -> [. A / x ]. ps ) ) ) $=
    ( wi wal wsbc frege65c frege8 ax-mp ) CAFDGZABFDGZCDEHBDEHFZFFMLNFFCABDEILM
    NJK $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 67 of [Frege1879] p. 54.  (Contributed by Richard Penner,
     8-Oct-2019.) $)
  frege67c $p |- ( ( ( A. x ph <-> ps ) -> ( ps -> A. x ph ) )
                   -> ( ( A. x ph <-> ps ) -> ( ps -> [. A / x ]. ph ) ) ) $=
    ( wal wsbc wi wb frege58c frege7 ax-mp ) ACEZACDFZGLBHZBLGGNBMGGGACDILMNBJK
    $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 68 of [Frege1879] p. 54. $)
  frege68c $p |- ( ( A. x ph <-> ps ) -> ( ps -> [. A / x ]. ph ) ) $=
    (  ) ? $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _Begriffschift_ Chapter III
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

   ` ( R " A ) C_ A ` means membership in ` A ` is hereditary in the
   sequence dictated by relation ` R ` .

$)

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

  $( PLEASE PUT DESCRIPTION HERE.

     Definition 69 of [Frege1879] p. 55. $)
  frege69c $p |- ( A. x ( x e. A -> A. y ( x R y -> y e. A ) )
                  <-> ( R " A ) C_ A ) $=
    (  ) ? $.

  $( Equivalent to ~ frege69 .

     Definition 69 of [Frege1879] p. 55. $)
  frege69eq $p |- ( ( R " A ) C_ A <-> ( R |` A ) C_ ( A X. A ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 70 of [Frege1879] p. 58. $)
  frege70 $p |- ( ( R " A ) C_ A -> ( x e. A -> A. y ( x R y -> y e. A ) ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 71 of [Frege1879] p. 59.  (Contributed by Richard Penner,
     29-Oct-2019.) $)
  frege71 $p |- ( ( A. z ( x R z -> z e. A ) -> ( x R y -> y e. A ) )
                  -> ( ( R " A ) C_ A
                       -> ( x e. A -> ( x R y -> y e. A ) ) ) ) $=
    ( cima wss cv wcel wbr wi wal frege70 frege19 ax-mp ) EDFDGZAHZDIZQCHZEJSDI
    KCLZKKTQBHZEJUADIKZKPRUBKKKACDEMPRTUBNO $.

  ${
    $d c A $.  $d c R $.  $d c x $.  $d c y $.
    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 72 of [Frege1879] p. 59.  (Contributed by Richard Penner,
       29-Oct-2019.) $)
    frege72 $p |- ( ( R " A ) C_ A -> ( x e. A -> ( x R y -> y e. A ) ) ) $=
      ( vc cv wbr wcel wi wal cima wss frege58c sbcim1 csb cvv ax-mp biimpi syl
      wsbc wb vex sbcbr2g weq wceq id ax-gen nfcv csbieb breq2i biimpri sbcel1v
      bitri imim12i frege71 ) AFZEFZDGZUQCHZIZEJZUPBFZDGZVBCHZIZIDCKCLUPCHVEIIV
      AUTEVBTZVEUTEVBMVFUREVBTZUSEVBTZIVEURUSEVBNVCVGVHVDVGVCVGUPEVBUQOZDGZVCVB
      PHVGVJUABUBZEVBUPUQDPUCQVIVBUPDEBUDZVLIZEJZVIVBUEZVMEVLUFUGVNVOEVBUQVBVKE
      VBUHUIRQUJUMUKVHVDEVBCULRUNSSABECDUOQ $.
  $}

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 73 of [Frege1879] p. 59. $)
  frege73 $p |- ( ( ( R " A ) C_ A -> x e. A )
                  -> ( ( R " A ) C_ A -> ( x R y -> y e. A ) ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 74 of [Frege1879] p. 60. $)
  frege74 $p |- ( x e. A -> ( ( R " A ) C_ A -> ( x R y -> y e. A ) ) ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 75 of [Frege1879] p. 60. $)
  frege75 $p |- ( A. x ( x e. A -> A. y ( x R y -> y e. A ) )
                  -> ( R " A ) C_ A ) $=
    (  ) ? $.

  ${
    frege76.f $e |- F = { <. p , c >. | c e. |^| { f | ( ( R " { p } ) C_ f
                                                          /\ ( R " f ) C_ f )
                                                  }
                         } $.
    ${
      frege76.r $e |- R = { <. x , y >. | ps } $.
      $( PLEASE PUT DESCRIPTION HERE.

         Proposition 76 of [Frege1879] p. 60. $)
      frege76 $p |- ( A. f ( ( R " f ) C_ f
                      -> ( A. a ( [ b / x ] [ a / y ] ps -> a e. f )
                           -> e e. f ) ) <-> b F e ) $=
        (  ) ? $.
    $}

    $( PLEASE PUT DESCRIPTION HERE.

       Proposition 76 of [Frege1879] p. 60. $)
    frege76eq $p |- ( B F E <-> ( B e. _V /\
                                  A. f ( ( R " { B } ) C_ f /\ ( R " f ) C_ f
                                         /\ E e. f ) ) ) $=
      (  ) ? $.
  $}

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 77 of [Frege1879] p. 62. $)
  frege77 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 78 of [Frege1879] p. 63. $)
  frege78 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 79 of [Frege1879] p. 63. $)
  frege79 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 80 of [Frege1879] p. 63. $)
  frege80 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 81 of [Frege1879] p. 63. $)
  frege81 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 82 of [Frege1879] p. 64. $)
  frege82 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 83 of [Frege1879] p. 65. $)
  frege83 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 84 of [Frege1879] p. 65. $)
  frege84 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 85 of [Frege1879] p. 66. $)
  frege85 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 86 of [Frege1879] p. 66. $)
  frege86 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 87 of [Frege1879] p. 66. $)
  frege87 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 88 of [Frege1879] p. 67. $)
  frege88 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 89 of [Frege1879] p. 68. $)
  frege89 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 90 of [Frege1879] p. 68. $)
  frege90 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 91 of [Frege1879] p. 68. $)
  frege91 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 92 of [Frege1879] p. 69. $)
  frege92 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 93 of [Frege1879] p. 70. $)
  frege93 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 94 of [Frege1879] p. 70. $)
  frege94 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 95 of [Frege1879] p. 70. $)
  frege95 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 96 of [Frege1879] p. 71. $)
  frege96 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 97 of [Frege1879] p. 71. $)
  frege97 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 98 of [Frege1879] p. 71. $)
  frege98 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 99 of [Frege1879] p. 71. $)
  frege99 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 100 of [Frege1879] p. 72. $)
  frege100 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 101 of [Frege1879] p. 72. $)
  frege101 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 102 of [Frege1879] p. 72. $)
  frege102 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

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

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 115 of [Frege1879] p. 77. $)
  frege115 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

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
  frege126 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 127 of [Frege1879] p. 82. $)
  frege127 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 128 of [Frege1879] p. 83. $)
  frege128 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 129 of [Frege1879] p. 83. $)
  frege129 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 130 of [Frege1879] p. 84. $)
  frege130 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 131 of [Frege1879] p. 85. $)
  frege131 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 132 of [Frege1879] p. 86. $)
  frege132 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

  $( PLEASE PUT DESCRIPTION HERE.

     Proposition 133 of [Frege1879] p. 86. $)
  frege133 $p |- ( ph -> -. ph ) $=
    (  ) ? $.

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

  $( Simplification of triple conjunction.  Compare with ~ simp2 .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  simp2frege $p |- ( ph -> ( ps -> ( ch -> ps ) ) ) $=
    ( wi ax-1 ax-mp ) BCBDDZAGDBCEGAEF $.

  $( More general statement than ~ frege3 .  Like ~ ax-2 , it is essentially a
     closed form of ~ mpd , however it has an extra antecedent.

     It would be more natural to prove from ~ a1i and ~ ax-2 in Metamath.
     (Contributed by Richard Penner, 1-Oct-2019.) $)
  frege3gen $p |- ( ph
                    -> ( ( ps -> ( ch -> th ) )
                         -> ( ( ps -> ch ) -> ( ps -> th ) ) ) ) $=
    ( wi ax-2 ax-1 ax-mp ) BCDEEBCEBDEEEZAIEBCDFIAGH $.

  $( Specialized form of ~ idd .

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  iddspfrege $p |- ( ( ph -> ps ) -> ( ph -> ph ) ) $=
    ( wi ax-1 ax-2 ax-mp ) ABACCABCAACCABDABAEF $.

  $( Double-use of ~ ax-2 .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  misc1frege $p |- ( ( ( ph -> ( ps -> ch ) ) -> ( ph -> ps ) )
                     -> ( ( ph -> ( ps -> ch ) ) -> ( ph -> ch ) ) ) $=
    ( wi ax-2 ax-mp ) ABCDDZABDZACDZDDGHDGIDDABCEGHIEF $.

  $( Simplify when consequent is also third antecedent.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  simprlfrege $p |- ( ph -> ( ps -> ( ch -> ( th -> ch ) ) ) ) $=
    ( wi simp2frege ax-1 ax-mp ) BCDCEEEZAIEBCDFIAGH $.

  $( Distribution with two unnecessary antecendents.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  misc3frege $p |- ( ph
                     -> ( ps
                          -> ( ( ch -> ( th -> ta ) )
                               -> ( ( ch -> th ) -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege3gen ax-1 ax-mp ) BCDEFFCDFCEFFFFZAJFBCDEGJAHI $.

  $( Introducing an embedded antecedent.  Alternate proof for ~ frege24 .
     Closed form for ~ a1d .

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  frege24ALT $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    ( wi simp2frege ax-2 ax-mp ) ABCBDZDDABDAHDDABCEABHFG $.

  ${
    a1dfrege.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.  Identical to ~ a1d .

       (Contributed by Richard Penner, 4-Oct-2019.) $)
    a1dfrege $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi frege24ALT ax-mp ) ABEACBEEDABCFG $.
  $}

  $( Simplify when consequent is also the first antecedent.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  simp1frege $p |- ( ph -> ( ps -> ( ch -> ph ) ) ) $=
    ( wi ax-1 frege24ALT ax-mp ) ACADZDABHDDACEAHBFG $.

  $( Deduction relatied to distribution.

     (Contributed by Richard Penner, 6-Oct-2019.) $)
  frege3gendist $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                        -> ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) ) $=
    ( wi frege3gen ax-2 ax-mp ) ABCDEEZBCEBDEEZEEAIEAJEEABCDFAIJGH $.

  $( Elimination of a nested antecedent of special form.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp4frege $p |- ( ( ph -> ( ( ps -> ph ) -> ch ) ) -> ( ph -> ch ) ) $=
    ( wi simp2frege misc1frege ax-mp ) ABADZCDDZAHDDIACDDIABEAHCFG $.

  ${
    rp4fregei.1 $e |- ( ph -> ( ( ps -> ph ) -> ch ) ) $.
    $( More naturally proved in Metamath from ~ ax-1 and ~ mpd .

       (Contributed by RichardPenner, 5-Oct-2019.) $)
    rp4fregei $p |- ( ph -> ch ) $=
      ( wi rp4frege ax-mp ) ABAECEEACEDABCFG $.
  $}

  $( Distribute antecedent and add another.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp7frege $p |- ( ( ph -> ( ps -> ch ) )
              -> ( th -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) ) $=
    ( wi ax-2 frege24ALT ax-mp ) ABCEEZABEACEEZEIDJEEABCFIJDGH $.

  $( Elimination of a nested antecedent of special form.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp6frege $p |- ( ph
                   -> ( ( ps -> ( ( ch -> ps ) -> th ) ) -> ( ps -> th ) ) ) $=
    ( wi rp4frege ax-1 ax-mp ) BCBEDEEBDEEZAIEBCDFIAGH $.

  $( Eliminate antecedent when it is implied by previous antecedent.

     (Contributed by Richard Penner, 2-Oct-2019.) $)
  rp8frege $p |- ( ( ph -> ( ps -> ( ( ch -> ps ) -> th ) ) )
                   -> ( ph -> ( ps -> th ) ) ) $=
    ( wi rp6frege ax-2 ax-mp ) ABCBEDEEZBDEZEEAIEAJEEABCDFAIJGH $.

  $( Swap antecedents.  Identical to ~ pm2.04 .

     Proof follows closely proof of ~ pm2.04 in
     ~ http://us.metamath.org/mmsolitaire/pmproofs.txt , but in the style of
     [Frege1879] .

     This demonstrates that Axiom 8 of [Frege1879] p. 35 is redundant.

     (Contributed by Richard Penner, 1-Oct-2019.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  frege8ALT $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi rp7frege rp8frege ax-mp ) ABCDDZBABDACDZDDDHBIDDABCBEHBAIFG $.
