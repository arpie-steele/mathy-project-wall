$[ set.mm $]

$(

  Add to #bib section of mmset.raw.html :

  <LI><A NAME="Dence1983"></A> [Dence1983] Thomas P. Dence, <I>Solving
  Math Problems in B.A.S.I.C.</I>, TAB Books, Blue Ridge Summit,
  PA. (1983) QA76.95 D46;</LI>

$)

$(
  MSC Classification 11A63 ( and 11A51 )
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

  In this subsection, the theorems work on the non-degenerate
  two-digit case in arbitrary base, ` B ` . Thus ` T ` is reserved
  for the "tens" digit and ` U ` is the "units" digit. ` W ` was
  chosen to represent the common digit which is targetted by the
  improper procedure. We always represent a two digit number as
  ` ( ( B x. T ) + U ) ` so that we may easily leverage the decimal
  operator for the ` B = 10 ` case.
$)

  ${

    rp-propercan.a $e |- ( ph -> A e. CC ) $.
    rp-propercan.b $e |- ( ph -> B e. CC ) $.
    rp-propercan.bne0 $e |- ( ph -> B =/= 0 ) $.
    rp-propercan.c $e |- ( ph -> C e. CC ) $.
    rp-propercan.cne0 $e |- ( ph -> C =/= 0 ) $.
    $( Proper cancellation when common factor multiplies from the front.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan3 $p |- ( ph -> ( ( B x. A ) / ( B x. C ) ) = ( A / C ) ) $=
      ( divcan5d ) ABDCEHFIGJ $.

    $( Proper cancellation when common factor is in the interior.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan1 $p |- ( ph -> ( ( A x. B ) / ( B x. C ) ) = ( A / C ) ) $=
      ( cmul co cdiv wceq rp-propercan3 mulcomd oveq1d eqeq1d mpbid ) ACBJKZ
      CDJKZLKZBDLKZMBCJKZTLKZUBMABCDEFGHINAUAUDUBASUCTLACBFEOPQR $.

    $( Proper cancellation when common factor is last.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan2 $p |- ( ph -> ( ( A x. B ) / ( C x. B ) ) = ( A / C ) ) $=
      ( divcan5rd ) ABDCEHFIGJ $.

    $( Proper cancellation when common factor is on exterior.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan4 $p |- ( ph -> ( ( B x. A ) / ( C x. B ) ) = ( A / C ) ) $=
      ( cmul co cdiv wceq rp-propercan2 mulcomd oveq1d eqeq1d mpbid ) ABCJKZ
      DCJKZLKZBDLKZMCBJKZTLKZUBMABCDEFGHINAUAUDUBASUCTLABCEFOPQR $.
  $}

  ${
    rp-propercan.acn $e |- ( ph -> A e. CC ) $.
    rp-propercan.ccn $e |- ( ph -> C e. CC ) $.
    rp-propercan.cne $e |- ( ph -> C =/= 0 ) $.
    $( Proper cancellation when common factor is 10 and we use the decimal
       operator to represent two-digit terms.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan5 $p |- ( ph -> ( ; A 0 / ; C 0 ) = ( A / C ) ) $=
      ( c10 cmul cdiv wceq cc0 cdc 10nn a1i caddc df-dec mulcld addid1d eqtr2d
      co cc wcel nncni wne nnne0i rp-propercan3 oveq12d eqeq1d mpbid ) AGBHT
      ZGCHTZITZBCITZJBKLZCKLZITZUMJABGCDGUAUBAGMUCNZGKUDAGMUENEFUFAULUPUMAUJUNU
      KUOIAUNUJKOTZUJUNURJABKPNAUJAGBUQDQRSAUOUKKOTZUKUOUSJACKPNAUKAGCUQEQRSUGU
      HUI $.
  $}

  ${
    rp-propercan.ann0 $e |- ( ph -> A e. NN0 ) $.
    rp-propercan.cnn $e |- ( ph -> C e. NN ) $.
    $( Proper cancellation when common factor is 10 and we use the decimal
       operator to represent two-digit terms.
       (Contributed by Richard Penner, 25-Oct-2019.) $)
    rp-propercan6 $p |- ( ph -> ( ; A 0 / ; C 0 ) = ( A / C ) ) $=
      ( cn0 wcel cc nn0cn syl cn nncn cc0 wne nnne0 rp-propercan5 ) ABCABFGB
      HGDBIJACKGZCHGECLJAQCMNECOJP $.
  $}

  $( "We all know that 9/12 is equivalent to 3/4". -Thomas P. Dence.

     Statement of [Dence1983] p. 39. 
     (Contributed by Richard Penner, 25-Oct-2019.) $)
  rp-propercanex1 $p |- ( 9 / ; 1 2 ) = ( 3 / 4 ) $=
    ( c9 c1 c2 cdiv co c3 cmul c4 3t3e9 eqcomi 4t3e12 oveq12i wceq wtru cc wcel
    cdc a1i cc0 wne 3cn 3ne0 4cn 4ne0 rp-propercan4 trud eqtri ) ABCQZDEFFGEZHF
    GEZDEZFHDEZAUIUHUJDUIAIJUJUHKJLUKULMNFFHFOPNUARZUMFSTNUBRHOPNUCRHSTNUDRUEUF
    UG $.

  $( "We all know ... that 21/56 is equivalent to 3/8." -Thomas P. Dence.

     Statement of [Dence1983] p. 39. 
     (Contributed by Richard Penner, 25-Oct-2019.) $)
  rp-propercanex2 $p |- ( ; 2 1 / ; 5 6 ) = ( 3 / 8 ) $=
    ( c2 c1 cdc c5 c6 cdiv co c7 c3 cmul c8 7t3e21 eqcomi wtru wcel a1i cc0 wne
    cc nnne0i 8t7e56 oveq12i wceq 3cn 7cn 7nn 8cn 8nn rp-propercan4 trud eqtri
    ) ABCZDECZFGHIJGZKHJGZFGZIKFGZULUNUMUOFUNULLMUOUMUAMUBUPUQUCNIHKISONUDPHSON
    UEPHQRNHUFTPKSONUGPKQRNKUHTPUIUJUK $.

  $( "It is somewhat interesting to note that 16/64 is equal to 1/4". -Thomas
     P. Dence.

     Statement of [Dence1983] p. 39. 
     (Contributed by Richard Penner, 25-Oct-2019.) $)
  rp-propercanex3 $p |- ( ; 1 6 / ; 6 4 ) = ( 1 / 4 ) $=
    ( c1 c6 cdc c4 cdiv co cmul c8 8p8e16 8cn eqeltrri eqtr2i 4cn wtru wcel a1i
    cc c2 cc0 8re caddc addcli mulid2i eqcomi 2timesi oveq2i 2cn mulassi oveq1i
    4t2e8 3eqtr2i 8t8e64 oveq12i wceq 1cnd wne cr readdcli clt addgt0ii breqtri
    8pos gt0ne0ii 4ne0 rp-propercan2 trud eqtri ) ABCZBDCZEFAVHGFZDVHGFZEFZADEF
    ZVHVJVIVKEVJVHVHHHUAFZVHQIHHJJUBKZUCUDVKHHGFZVIVKDRHGFZGFDRGFZHGFVPVHVQDGVQ
    VNVHHJUEILUFDRHMUGJUHVRHHGUJUIUKULLUMVLVMUNNAVHDNUOVHQONVOPVHSUPNVHVNVHUQIH
    HTTURKSVNVHUSHHTTVBVBUTIVAVCPDQONMPDSUPNVDPVEVFVG $.

  $( "The fraction 19/95 is equal to 1/5". -Thomas P. Dence.

     Statement of [Dence1983] p. 39. 
     (Contributed by Richard Penner, 26-Oct-2019.) $)
  rp-propercanex4 $p |- ( ; 1 9 / ; 9 5 ) = ( 1 / 5 ) $=
  ( c1 c9 cdc c5 cdiv co cmul c10 caddc wcel 10nn eqcomi cc0 5cn oveq12i 3eqtri
  cn c4 wtru a1i dec10p 9nn nnaddcl mp2an eqeltrri mulid2i df-dec oveq2i oveq1i
  nncni 5p4e9 adddii mulcli addassi 5nn0 dec0u eqtri mulcomi eqtr2i 9t5e45 wceq
  4cn 9cn 1cnd cc wne nnne0i 5nn rp-propercan2 trud ) ABCZBDCZEFAVKGFZDVKGFZ
  EFZADEFZVKVMVLVNEVMVKVKVKHBIFZVKQBUAZHQJBQJVQQJKUBHBUCUDUEZUJZUFLVLHBGFZDIFZD
  MCZRDCZIFZVNBDUGWBHDRIFZGFZDIFHDGFZHRGFZIFZDIFZWEWAWGDIBWFHGWFBUKLUHUIWGWJDIH
  DRHKUJZNVBULUIWKWHWIDIFZIFWEWHWIDHDWLNUMHRWLVBUMNUNWHWCWMWDIDUOUPZWDWMRDUGLOU
  QPWEDHGFZDBGFZIFZDVQGFZVNWCWOWDWPIWOWHWCDHNWLURWNUSWPBDGFWDDBNVCURUTUSOWRWQDH
  BNWLVCULLVQVKDGVRUHPPOVOVPVASAVKDSVDVKVEJSVTTVKMVFSVKVSVGTDVEJSNTDMVFSDVHVGTV
  IVJUQ $.

  $( "Also 26/65 equals to 2/5". -Thomas P. Dence.

     Statement of [Dence1983] p. 40. 
     (Contributed by Richard Penner, 26-Oct-2019.) $)
  rp-propercanex5 $p |- ( ; 2 6 / ; 6 5 ) = ( 2 / 5 ) $=
    ( c2 c6 cdc c5 cdiv co c1 c3 cmul c10 caddc 2cn mulcomi 3cn eqtri wtru wcel
    5cn a1i cn df-dec 10nn nncni 3t2e6 eqcomi oveq12i adddii dec10p oveq2i df-6
    3eqtr2i oveq1i ax-1cn 3eqtri mulcli addassi mulid1i 5t3e15 wceq 3nn nnaddcl
    cc mp2an eqeltrri cc0 wne nnne0i 5nn rp-propercan2 trud ) ABCZBDCZEFAGHCZIF
    ZDVMIFZEFZADEFZVKVNVLVOEVKAJIFZAHIFZKFZAJHKFZIFVNVKJAIFZBKFVTABUAWBVRBVSKJA
    JUBUCZLMBHAIFZVSWDBUDUEHANLMOUFOAJHLWCNUGWAVMAIHUHZUIUKVLDJIFZDHIFZKFZDWAIF
    VOVLJDIFZJGIFZKFZDKFZWIWJDKFZKFWHVLJBIFZDKFJDGKFZIFZDKFWLBDUAWNWPDKBWOJIUJU
    IULWPWKDKJDGWCRUMUGULUNWIWJDJDWCRUOJGWCUMUORUPWIWFWMWGKJDWCRMWMJDKFGDCZWGWJ
    JDKJWCUQULDUHWGWQURUEUNUFUNDJHRWCNUGWAVMDIWEUIUKUFVPVQUSPAVMDAVBQPLSVMVBQPV
    MWAVMTWEJTQHTQWATQUBUTJHVAVCVDZUCSVMVEVFPVMWRVGSDVBQPRSDVEVFPDVHVGSVIVJO $.

  $( "484/847 = 4/7". -Thomas P. Dence.

     Statement of [Dence1983] p. 40. 
     (Contributed by Richard Penner, 26-Oct-2019.) $)
  rp-propercanex6 $p |- ( ; ; 4 8 4 / ; ; 8 4 7 ) = ( 4 / 7 ) $=
  ( c4 c8 cdc c7 co c1 c2 cmul c10 caddc df-dec nncni eqcomi oveq2i 3eqtri wcel
  4cn cn 7cn wtru cdiv 10nn mulcomi 4t2e8 oveq12i 2cn adddii eqtr4i 2nn nnaddcl
  dec10p mp2an eqeltri mul12i eqtri mulid1i nnmulcli ax-1cn df-8 oveq1i addassi
  7nn 7t2e14 wceq cc a1i 1nn cc0 wne nnne0i rp-propercan2 trud ) ABCZACZBACZDCZ
  UAEAFGCZFCZHEZDVRHEZUAEZADUAEZVNVSVPVTUAVNIVMHEZAJEZAIVQHEZFJEZHEZVSVMAKWDAWE
  HEZAFHEZJEWGWCWHAWIJWCIAVQHEZHEWHVMWJIHVMIAHEZBJEZAIGJEZHEZWJABKWLAIHEZAGHEZJ
  EWNWKWOBWPJIAIUBLZQUCWPBUDMUEAIGQWQUFUGUHWMVQAHGUKZNONIAVQWQQVQVQWMRWMVQWRMIR
  PGRPWMRPUBUIIGUJULUMZLZUNUOWIAAQUPMUEAWEFQWEIVQUBWSUQZLZURUGUHWFVRAHVRWFVQFKZ
  MZNOVPIVOHEZDJEZDWFHEZVTVODKXFDWEHEZDFHEZJEXGXEXHDXIJXEIDVQHEZHEXHVOXJIHVOIBH
  EZAJEZDWMHEZXJBAKXLIDHEZIAJEZJEZDIHEZDGHEZJEZXMXLXNIJEZAJEXPXKXTAJXKIDFJEZHEX
  NIFHEZJEXTBYAIHUSNIDFWQSURUGYBIXNJIWQUPNOUTXNIAXNIDUBVBUQLWQQVAUOXNXQXOXRJIDW
  QSUCXOFACXRAUKVCUHUEXMXSDIGSWQUFUGMOWMVQDHWRNONIDVQWQSWTUNUOXIDDSUPMUEDWEFSXB
  URUGUHWFVRDHXDNOUEWAWBVDTAVRDAVEPTQVFVRVEPTVRVRWFRXCWERPFRPWFRPXAVGWEFUJULUMZ
  LVFVRVHVITVRYCVJVFDVEPTSVFDVHVITDVBVJVFVKVLUO $.

  ${
    rp-anomcanlem.b $e |- ( ph -> B e. CC ) $.
    rp-anomcanlem.w $e |- ( ph -> W e. CC ) $.
    rp-anomcanlem.t $e |- ( ph -> T e. CC ) $.
    rp-anomcanlem.u $e |- ( ph -> U e. CC ) $.
    rp-anomcanlem.une0 $e |- ( ph -> U =/= 0 ) $.
    rp-anomcanlem.demne0 $e |- ( ph -> ( ( B x. W ) + U ) =/= 0 ) $.
    ${
      rp-anomcanlem.canw $e |- ( ph -> U =/= ( B x. T ) ) $.
      $( Working in base ` B ` , if the fraction
         ` ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) ) ` is equal to the result
         of incorrectly cancelling the common digit ` W ` iff that common digit
         has a value determined only by ` B ` , ` T ` , and ` U ` .  The
         condition ` U =/= ( B x. T ) ` is eliminated. 
         (Contributed by Richard Penner, 26-Oct-2019.) $)
      rp-anomcanlem1 $p |- ( ph
                         -> ( ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) )
                              = ( T / U )
                            <-> W = ( ( ( B - 1 ) x. ( T x. U ) )
                                      / ( ( B x. T ) - U ) ) ) ) $=
        ( cmul co caddc cdiv wceq c1 cmin mulcld addcld adddird eqeq12d addcomd
        divmuleqd adddid eqeq1d addsubeq4d mul12d mulcomd oveq2d 3eqtrd mulassd
        oveq1d mulid2d eqcomd oveq12d subdird eqtr4d wb eqcom a1i subdid subcld
        1cnd wcel wne cc0 w3a simp1 simp2 simp3 necomd subne0d syl3anc divmul3d
        cc 3bitr4d 3bitrd ) ABCMNZEONZBEMNZDONZPNCDPNQWADMNZCWCMNZQVTDMNZEDMNZO
        NZCWBMNZCDMNZONZQZEBRSNZWJMNZVTDSNZPNZQZAWAWCCDAVTEABCFHTZGUAAWBDABEFGT
        ZIUAHIKJUEAWDWHWEWKAVTEDWRGIUBACWBDHWSIUFUCAWLWGWFONZWKQWIWGSNZWFWJSNZQ
        ZWQAWHWTWKAWFWGAVTDWRITZAEDGITZUDUGAWGWFWIWJXEXDACWBHWSTACDHITZUHAXCEVT
        MNZWGSNZWNQZWPEQZWQAXAXHXBWNAWIXGWGSAWIBCEMNZMNBECMNZMNXGACBEHFGUIAXKXL
        BMACEHGUJUKABECFGHUIULUNAXBBWJMNZRWJMNZSNWNAWFXMWJXNSABCDFHIUMAXNWJAWJX
        FUOUPUQABRWJFAVEZXFURUSUCAEWOMNZWNQZWNXPQZXIXJXQXRUTAXPWNVAVBAXHXPWNAXP
        XHAEVTDGWRIVCUPUGAWNEWOAWMWJABRFXOVDXFTGAVTDWRIVDAVTVQVFZDVQVFZDVTVGZWO
        VHVGWRILXSXTYAVIZVTDXSXTYAVJXSXTYAVKYBDVTXSXTYAVLVMVNVOVPVRXJWQUTAWPEVA
        VBVSVSVS $.
    $}

    ${
      rp-anomcanlem.cantw $e |- ( ph -> U = ( B x. T ) ) $.
      $( Working in base ` B ` , if the fraction
         ` ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) ) ` is equal to the result
         of incorrectly cancelling the common digit ` W ` , the additional
         condition, ` U = ( B x. T ) ` , results in a sterile result. 
         (Contributed by Richard Penner, 26-Oct-2019.) $)
      rp-anomcanlem2 $p |- ( ph
                         -> ( ( ( ( B x. T ) + W ) / ( ( B x. W ) + U ) )
                              = ( T / U ) -> ( B = 1 /\ T = U ) ) ) $=
        ( cmul co caddc cdiv wceq c1 eqcomd eqeq2d oveq2d adantr 3eqtrd eqnetrd
        wa simpr mulcld addcld cc0 eqnetrrd divmuleqd biimpa wi mulassd mulcomd
        adddid oveq1d mulcan2d 3bitrd addcomd eqeq1d addcand bitrd mulid2d 1cnd
        mulne0bbd biimpd mpd syldan ad2antrr cc wcel 3eqtr2rd jca mpdan ex ) AB
        CMNZEONZBEMNZDONZPNZCDPNZQZBRQZCDQZUEZAWCUEZWDWFAWCVRVSVQONZPNZCVQPNZQZ
        WDWGWIWAWBWJAWIWAQWCAWHVTVRPAVQDVSOADVQLSUAZUAUBAWCUFAWBWJQWCADVQCPLUAU
        BUCAWKUEVRVQMNZCWHMNZQZWDAWKWOAVRWHCVQAVQEABCFHUGZGUHZAVSVQABEFGUGWPUHH
        WPAWHVTUIWLKUDADVQUILJUJZUKULAWOWDUMWKAWOWDAWOVRECONZQZVQCQZWDAWOWMCBWS
        MNZMNZQWMCBMNZWSMNZQZWTAWNXCWMAWHXBCMAXBWHABECFGHUPSUATAXCXEWMAXEXCACBW
        SHFAECGHUHZUNSTAXFWMVQWSMNZQWMWSVQMNZQWTAXEXHWMAXDVQWSMACBHFUOUQTAXHXIW
        MAVQWSWPXGUOTAVRWSVQWQXGWPWRURUSUSAWTEVQONZWSQXAAVRXJWSAVQEWPGUTVAAEVQC
        GWPHVBVCAXAVQRCMNZQWDACXKVQAXKCACHVDSTABRCFAVEHABCFHWRVFURVCUSVGUBVHVIW
        GWDUEZWDWEWGWDUFZXLDVQXKCADVQQWCWDLVJXLRBCMXLBRXMSUQXLCACVKVLWCWDHVJVDV
        MVNVOVP $.
    $}
  $}
