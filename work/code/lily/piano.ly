\header {
  copyright  = "Copyright \copyright 2005 Luke Palmer"
  title      = "Concerto for Piano"
  composer   = "Luke Palmer"
  instrument = "Piano"
  piece      = "I. Allegro ma non troppo"
}

% Theme A, intro

themeAAright = \relative b' {
  \clef treble
  \key b \minor
  \time 4/4

  r1 r1
  b8\f d fis b ais gis fis4
  g8 fis e fis d cis fis,4
  g8 b d g fis e fis4
  g,8 e d' b gis' eis fis, \times 2/3 { fis'16 fis fis } 
  
  b,8\ff d fis b ais gis fis4
  g8 fis e fis d cis fis,4
  g8 c e g fis e fis4
  <fis, fis,>8 <e e,> <d' d,> <b b,> 
    \times 2/3 { <e e,> <cis cis,> <b b,> } <ais ais,>4~
  
  <ais g ais,>1\mf
  <g' ais,>
  <e, ais g'>\arpeggio\f~
  <e ais g'>
}

themeAAleft = \relative b {
  \clef treble
  \key b \minor
  \time 4/4
  
  r1 r1
  b8 d fis b ais gis fis4
  g8 fis e fis d cis fis,4
  g8 b d g fis e fis4
  g,8 e d' b gis' eis fis, r

  \clef bass
  <b b,> <d d,> <fis fis,> <b b,> <ais ais,> <gis gis,> <fis fis,>4
  <g g,>8 <fis fis,> <e e,> <fis fis,> <d d,> <cis cis,> <fis, fis,>4
  <g g,>8 <c c,> <e e,> <g g,> <fis fis,> <e e,> <fis fis,>4
  fis,,8 e d' b e g cis4~
  
  <cis e>1
  \clef treble
  <e cis'>
  \clef bass
  <e,, cis' b'>\arpeggio~
  <e cis' b'>
}

% Theme B, initial development

themeBAbase = \relative b, {
  b16 d cis d e d cis d b d ees d cis d e-> d
  f-> d cis d b d fis-> d g-> ees d ees gis-> e dis e
  g-> d cis d b d fis-> d gis-> e dis e b e d e
  gis-> e dis e fis d cis d b'-> fis e fis dis fis b-> fis
}

themeBAright = \relative b {
  \clef bass
  << \themeBAbase { s1\f } >>
  a16( fis cis fis 
    \clef treble
    cis' a fis' cis) 
    g'( e b e b' dis, fis a)
  gis( e cis' a) dis( b fis dis' e a, gis eis') fis( a, ais g')
  fis\<( dis a fis) g( e cis g) dis''( a fis dis)
    \clef bass
    cis( g e b)\!
  fis\ff( g a g fis a g fis) e cis dis e a, d cis c

  r\fp a' fis g cis fis, a g r a fis g cis fis, a g
  r a fis g d' g, b a r a fis g d' gis, b a
  r a fis gis d' gis, b ais r ais fis g e' g, b a
  r b fis g fis' gis, b cis g' d cis g fis e d cis
  b fis' b d fis\< ais b cis d fis,( a b
    \clef treble
    d fis g a)\!
}

themeBAleft = \relative b, {
  \transpose b b, \themeBAbase
  a( fis cis fis cis' a fis' cis) 
    g'( e b e b' dis, fis a)
  gis( e cis' a) dis( b fis dis' e a, gis eis') fis( a, ais g')
  fis( dis a fis) g( e cis g) dis''( a fis dis) cis( g e b)
  #(set-octavation -1)
  fis( g a g fis a g fis) e cis dis e a, d cis c
  
  << 
    { b2 b b b b b }
    { b'2 b b b b b }
  >>
  << b,4 b'4 >>
  #(set-octavation 0)
    fis' g fis,
  b fis'8 d' fis g b cis
}

righthand = {
  \themeAAright
  R1*8
  \themeBAright
}

lefthand = {
  \themeAAleft
  R1*8
  \themeBAleft
}

\score {
  \context PianoStaff <<
    \set Score.skipBars = ##t
    \set PianoStaff.connectArpeggios = ##t
    \context Staff = righthand \righthand
    \context Staff = lefthand \lefthand
  >>
  \layout { }
}
