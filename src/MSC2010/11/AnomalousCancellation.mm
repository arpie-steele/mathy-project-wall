$[ set.mm $]

$(

  Add to #bib section of mmset.raw.html :

  <LI><A NAME="Dence1983"></A> [Dence1983] Thomas P. Dence, <I>Solving
  Math Problems in B.A.S.I.C.</I>, TAB Books, Blue Ridge Summit,
  PA. (1983) QA76.95 D46;</LI>

$)

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
     Number Theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
        Anomalous Cancellation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Proper cancellation is reducing the magnitude of numerators and
  denominators by cancelling common non-zero factors.  Example:
  ` |- ( ( 1 x. 6 ) / ( 6 x. 4 ) ) = ( 1 / 4 ) ` . See ~ divcan5 .

  Since multiplication by 10 (in base 10) is the same as a positional
  shift by adding a zero the the right, proper cancellation by
  removing common powers of 10 is equivalent to removing the same
  number of zeros on the right.  Example:
  ` |- ( ( ; 1 0 ) / ( ; 4 0 ) ) = ( 1 / 4 ) ` . See ~ dec0u .

  Anomolous Cancellation is the faulty mathematical procedure of
  removing identical digits from numerator and denominator to in
  the event when the result in an equivalent fraction. Example:
  ` |- ( ; 1 6 / ; 6 4 ) = ( 1 / 4 ) ` .
$)

  $( Proper cancellation when common factor multiplies from the front.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan3 $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC )
                          /\ ( B =/= 0 /\ C =/= 0 ) )
                         -> ( ( B x. A ) / ( B x. C ) ) = ( A / C ) ) $=
    ( cc wcel w3a cc0 wne wa cmul co cdiv wceq simpl1 simp3 simpr anim12i simp2
    simpl 3jca divcan5 syl ) ADEZBDEZCDEZFZBGHZCGHZIZIZUCUEUHIZUDUGIZFBAJKBCJKL
    KACLKMUJUCUKULUCUDUEUINUFUEUIUHUCUDUEOUGUHPQUFUDUIUGUCUDUERUGUHSQTACBUAUB
    $.

  $( Proper cancellation when common factor is in the interior.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan1 $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC )
                          /\ ( B =/= 0 /\ C =/= 0 ) )
                         -> ( ( A x. B ) / ( B x. C ) ) = ( A / C ) ) $=
    ( cc wcel w3a cc0 wne wa cmul cdiv wceq rp-propercan3 simpl2 simpl1 mulcomd
    co oveq1d eqeq1d mpbid ) ADEZBDEZCDEZFBGHCGHIZIZBAJQZBCJQZKQZACKQZLABJQZUGK
    QZUILABCMUEUHUKUIUEUFUJUGKUEBAUAUBUCUDNUAUBUCUDOPRST $.

  $( Proper cancellation when common factor is last.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan2 $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC )
                          /\ ( B =/= 0 /\ C =/= 0 ) )
                        -> ( ( A x. B ) / ( C x. B ) ) = ( A / C ) ) $=
    ( cc wcel w3a cc0 wne wa cmul cdiv wceq rp-propercan1 simpl2 simpl3 mulcomd
    co oveq2d eqeq1d mpbid ) ADEZBDEZCDEZFBGHCGHIZIZABJQZBCJQZKQZACKQZLUFCBJQZK
    QZUILABCMUEUHUKUIUEUGUJUFKUEBCUAUBUCUDNUAUBUCUDOPRST $.

  $( Proper cancellation when common factor is on exterior.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan4 $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC )
                          /\ ( B =/= 0 /\ C =/= 0 ) )
                        -> ( ( B x. A ) / ( C x. B ) ) = ( A / C ) ) $=
    ( cc wcel w3a cc0 wne wa cmul cdiv wceq rp-propercan3 simpl2 simpl3 mulcomd
    co oveq2d eqeq1d mpbid ) ADEZBDEZCDEZFBGHCGHIZIZBAJQZBCJQZKQZACKQZLUFCBJQZK
    QZUILABCMUEUHUKUIUEUGUJUFKUEBCUAUBUCUDNUAUBUCUDOPRST $.

  $( Proper cancellation when common factor is 10 and we use the
     decimal operator to represent two-digit terms.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan5 $p |- ( ( A e. CC /\ C e. CC /\ C =/= 0 )
                        -> ( ; A 0 / ; C 0 ) = ( A / C ) ) $=
    ( cc wcel cc0 wne w3a c10 wa cdc cdiv wceq a1i jca cmul caddc df-dec mulcld
    co addid1d simp1 10nn0 nn0cni simp2 10pos gtneii simp3 rp-propercan3 simpl2
    3jca 0re simpl1 eqtr2d simpl3 oveq12d eqeq1d mpbid syl ) ACDZBCDZBEFZGZUSHC
    DZUTGZHEFZVAIZIZAEJZBEJZKSZABKSZLZVBVDVFVBUSVCUTUSUTVAUAVCVBHUBUCMUSUTVAUDU
    JVBVEVAVEVBEHUKUEUFMUSUTVAUGNNVGHAOSZHBOSZKSZVKLVLAHBUHVGVOVJVKVGVMVHVNVIKV
    GVHVMEPSZVMVHVPLVGAEQMVGVMVGHAUSVCUTVFUIZUSVCUTVFULRTUMVGVIVNEPSZVNVIVRLVGB
    EQMVGVNVGHBVQUSVCUTVFUNRTUMUOUPUQUR $.

  $( Proper cancellation when common factor is 10 and we use the
     decimal operator to represent two-digit terms.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercan6 $p |- ( ( A e. NN0 /\ C e. NN )
                        -> ( ; A 0 / ; C 0 ) = ( A / C ) ) $=
    ( cn0 wcel cn wa cc cc0 wne w3a cdiv co wceq nn0cn adantr nncn adantl nnne0
    cdc 3jca rp-propercan5 syl ) ACDZBEDZFZAGDZBGDZBHIZJAHSBHSKLABKLMUEUFUGUHUC
    UFUDANOUDUGUCBPQUDUHUCBRQTABUAUB $.

  $( "We all know that 9/12 is equivalent to 3/4". -Thomas P. Dence.

     Statement of [Dence1983] p. 39.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercanex1 $p |- ( 9 / ; 1 2 ) = ( 3 / 4 ) $=
    ( c9 c1 c2 cdc cdiv co c3 cmul c4 3t3e9 eqcomi 4t3e12 oveq12i cc cc0 wne wa
    wcel 3cn pm3.2i w3a wceq 4cn 3pm3.2i 3ne0 4ne0 rp-propercan4 ax-mp eqtri )
    ABCDZEFGGHFZIGHFZEFZGIEFZAUKUJULEUKAJKULUJLKMGNRZUOINRZUAZGOPZIOPZQZQUMUNUB
    UQUTUOUOUPSSUCUDURUSUEUFTTGGIUGUHUI $.

  $( "We all know ... that 21/56 is equivalent to 3/8." -Thomas P. Dence.

     Statement of [Dence1983] p. 39.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercanex2 $p |- ( ; 2 1 / ; 5 6 ) = ( 3 / 8 ) $=
    ( c2 c1 cdc c5 c6 cdiv co c7 c3 cmul c8 7t3e21 eqcomi cc wcel cc0 wa nnne0i
    wne pm3.2i oveq12i w3a wceq 3cn 7cn 8cn 3pm3.2i 7nn 8nn rp-propercan4 ax-mp
    8t7e56 eqtri ) ABCZDECZFGHIJGZKHJGZFGZIKFGZUNUPUOUQFUPUNLMUQUOULMUAINOZHNOZ
    KNOZUBZHPSZKPSZQZQURUSUCVCVFUTVAVBUDUEUFUGVDVEHUHRKUIRTTIHKUJUKUM $.

  $( "[I]t is somewhat interesting to note that 16/64 is equal to 1/4".
     -Thomas P. Dence.

     Statement of [Dence1983] p. 39.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercanex3 $p |- ( ; 1 6 / ; 6 4 ) = ( 1 / 4 ) $=
    ( c1 c6 c4 cdiv co cmul c8 cc wcel 8cn 8p8e16 ax-mp eqcomi c2 eqtri 4cn cc0
    cr 8re clt cdc caddc addcli eleq1i biimpi mulid2i 2timesi 2cn mulassi 4p4e8
    oveq2i mulcomi oveq1i 3eqtri 8t8e64 oveq12i w3a wne wa wceq ax-1cn readdcli
    3pm3.2i eleq1a wbr 8pos addgt0ii breq2i gt0ne0ii 4ne0 pm3.2i rp-propercan2
    wi ) ABUAZBCUAZDEAVNFEZCVNFEZDEZACDEZVNVPVOVQDVPVNVNGGUBEZHIZVNHIZGGJJUCWAW
    BVTVNHKUDUELZUFMVQVOVQGGFEZVOVQCNGFEZFEZCNFEZGFEZWDVNWECFWEVNWEVTVNGJUGKOMU
    KWHWFCNGPUHJUIMWGGGFWGNCFEZGCNPUHULWICCUBEGCPUGUJOOUMUNUOOMUPAHIZWBCHIZUQZV
    NQURZCQURZUSZUSVRVSUTWLWOWJWBWKVAWCPVCWMWNVNVNVTUTZVNRIZVTVNKMVTRIWPWQVMGGS
    SVBVTRVNVDLLQVTTVEZQVNTVEZGGSSVFVFVGWRWSVTVNQTKVHUELVIVJVKVKAVNCVLLO $.

  $( "The fraction 19/95 is equal to 1/5". -Thomas P. Dence.

     Statement of [Dence1983] p. 39.

     (Contributed by Richard Penner, 23-Oct-2019.) $)
  rp-propercanex4 $p |- ( ; 1 9 / ; 9 5 ) = ( 1 / 5 ) $=
    ( c1 c9 cdc c5 cdiv co cmul c10 caddc cc df-dec mulcli ax-mp eqcomi 5cn cc0
    wcel c4 eqtri oveq12i wceq wi 10nn0 nn0cni ax-1cn 9cn addcli eleq1a mulid2i
    oveq2i adddii mulid1i mulcomi addid1i 9t5e45 0cn 4cn add42i 5p4e9 3eqtri wa
    w3a wne 3pm3.2i 10re 1re remulcli 9re readdcli clt 10pos 0lt1 mulgt0ii 9pos
    cr wbr addgt0ii breq2i biimpi gt0ne0ii 5re 5pos pm3.2i rp-propercan2 ) ABCZ
    BDCZEFAWEGFZDWEGFZEFZADEFZWEWGWFWHEWGWEWEWEHAGFZBIFZUAZWEJQZABKZWLJQWMWNUBW
    KBHAHUCUDZUELZUFUGWLJWEUHMMZUINWHWFWHDWLGFDWKGFZDBGFZIFZWFWEWLDGWOUJDWKBOWQ
    UFUKXADPCZRDCZIFHDGFZPIFZHRGFZDIFZIFZWFWSXBWTXCIWSXEXBWSXDXEWSDHGFXDWKHDGHW
    PULUJDHOWPUMSXEXDXDHDWPOLZUNNSXBXEDPKZNSWTBDGFXCDBOUFUMUOSTXBXEXCXGIXJRDKTX
    HXDXFIFZDPIFZIFZWFXDPXFDXIUPHRWPUQLOURXMHBGFZDIFZWFXKXNXLDIXKHDRIFZGFZXNXQX
    KHDRWPOUQUKNXPBHGUSUJSDOUNTWFXOBDKNSSUTUTNTAJQZWNDJQZVBZWEPVCZDPVCZVAZVAWIW
    JUAXTYCXRWNXSUEWROVDYAYBWEWMWEVOQZWOWLVOQWMYDUBWKBHAVEVFVGZVHVIWLVOWEUHMMPW
    LVJVPZPWEVJVPZWKBYEVHHAVEVFVKVLVMVNVQYFYGWLWEPVJWEWLWONVRVSMVTDWAWBVTWCWCAW
    EDWDMS $.

  $( "Also 26/65 equals to 2/5". -Thomas P. Dence.

     Statement of [Dence1983] p. 40.

      $)
  rp-propercanex5 $p |- ( ; 2 6 / ; 6 5 ) = ( 2 / 5 ) $=
    ? $.

  $( "484/847 = 4/7". -Thomas P. Dence.

     Statement of [Dence1983] p. 40.

      $)
  rp-propercanex6 $p |- ( ; ; 4 8 4 / ; ; 8 4 7 ) = ( 4 / 7 ) $=
    ? $.