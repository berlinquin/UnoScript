# ( -- \ndlrow olleH )
y1y0
r1r0r0
y1y0y8
r1r1r4
y1y1y1
r1r1r9
y3y2
r1r1r1
y1y0y8
r1r0r8
y1y0y1
r7r2
# ( -- g0 b12 g8)
g0
b1b2
g8
# (g0 b12 g8 -- g0 b12 )
skip

# LOOP
g8

# ( g0 b12 -- g0 b12 g0 b12 )
draw4y1
# ( g0 b12 g0 b12 -- g0 b12 b(0 >= 12) )
draw2b3
# ( g0 b12 b(0 >= 12) -- g0 b12 b(0 >= 12) g9 )
g9
# ( g0 b12 b(0 >= 12) g9 -- g0 b12 )
draw2b2
# ( g0 b12 -- g0 b12 b9)
wild
b9
# ( g0 b12 -- )
skip
# END LOOP GUARD
g9

# ( x g0 b12 -- g0 b12 x )
draw4r2
# ( g0 b12 x -- g0 b12 )
draw2g2
# ( g0 b12 -- b12 g0 )
draw2r1
# ( b12 g0 -- b12 g0 g1 )
wild
g1
# ( b12 g0 b1 -- b12 b1 )
draw2r0
# ( b12 b1 -- b1 b12 )
draw2r1
# (b1 b12 -- b1 b12 g8 )
g8
# (b1 b12 g8 -- b1 b12 )
reverse

# END
b9
r9

