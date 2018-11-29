globals[colors n_all cost best_circuit iter_len occ nb_it heur nd]

breed[nodes node]


breed[ants ant]
ants-own [
  cur_node
  len_cir
  n_known
  n_left
]

links-own [
  len
  phe
]

to go
  while [ nb_it < ( cond - 1 ) ] [
    show "------------"
    show nb_it
    move_cir
    set nb_it ( nb_it + 1 )
    reset_ants

  ]

  show "fin de simulation"
  show best_circuit
  show cost
  ;check
  reset_global

end


to go_once
  move_once
end

to layout
  layout-spring nodes links 1 20 20
  ask ants[
    move-to cur_node
  ]
end

to clear_plot
  clear-plot
end

to setup
  ca

  set-current-plot "cout"
  ;; on arrete la simulation lorsque l'on trouve cond fois le meme cout pour le meilleur chemin

  set cost 0
  set best_circuit []
  set occ 0

  ask patches [ set pcolor white ]

  set colors [red blue green yellow]
  set n_all (range 0 nb_node )

  create-nodes nb_node
  [
    set shape "circle"
    setxy random pxcor random pycor
    set color one-of colors
  ]

  ask nodes [
    create-links-with n-of (nb_node - 1 ) other nodes
    setxy 0.95 * xcor 0.95 * ycor
  ]

  ask links[
    set color grey
    set len ( ( random 99 ) + 1 )
    set heur ( heur + len )
  ]
  repeat 5 [layout] ;; espacer les sommets

  heuris
  show "valeure heuristique"
  show heur

  set t0 ( 1 / ( heur * nb_node ) ) ;; (1/n*Lnn)
  set iter_len heur

  ask links [ set phe t0 ]


  create-ants nb_ant [
    set color black
    set shape "bug"

    set cur_node one-of nodes
    set n_known []
    set n_known ( lput ( [who] of cur_node ) n_known )
    set len_cir 0
    set n_left (remove ( [who] of cur_node ) n_all )

    move-to cur_node
  ]

  reset-ticks
end

to heuris
  create-ants 1[
    set color white
    set shape "bug"

    set cur_node one-of nodes
    ;show cur_node
    set n_known []
    set best_circuit (lput ([who] of cur_node ) best_circuit)

    set n_left (remove ( [who] of cur_node ) n_all )
    move-to cur_node
  ]
  ask ants [

    while [ not (empty? n_left ) ] [
      let min_l 10000
      foreach ( n_left ) [
        i_nd ->
        let lnk_len ( [len] of (link ([who] of cur_node) i_nd) )
        if ( lnk_len <= min_l ) [
          set min_l lnk_len
          set nd i_nd
        ]
      ]
      set cost (cost + min_l )
      set best_circuit ( lput nd best_circuit )
      set n_left ( remove nd n_left)

      set cur_node (node nd)
      move-to cur_node
    ]
    set cost ( cost + ( [len] of ( link ( first best_circuit) ( last best_circuit) ) ) ) ;; dernier chemin pour fermer le circuit
    set heur cost

    let i 0
    repeat ( ( length best_circuit ) - 1 ) [
      let n1 ( item i best_circuit )
      let n2 ( item ( i + 1 ) best_circuit )

      ask ( link n1 n2 ) [ set color red ]
      set i ( i + 1 )
  ]
    die
  ]
end

to move_cir
  let nb ( length n_all ) - 1
  while [ nb > 0 ] [
    move_once
    set nb ( nb - 1)
  ]
  ask ants[
    set len_cir ( len_cir + ( [len] of ( link ( first n_known ) ( last n_known ) ) ) ) ;; dernier chemin pour fermer le circuit
    set cur_node  ( node ( first n_known ) )
    move-to cur_node
  ]
  global_update
  tick


end

to move_once
  ask ants[
    let choice [] ;; liste dont les element sont [ id_node desirabilité ]
    let i 0
    let ttl 0

    if (empty? n_left) [ show "fin de parcours inattendue" ]
    foreach n_left [
      cand -> ;; indice d'un noeud candidat
      let idc ( [who] of cur_node )
      let lnk (link idc cand )

      let n_cand (node cand ) ;; le noeud candidat
      let phc ([phe] of lnk )
      let lnc ([len] of lnk )
      let val ( phc * ( ( 1 / lnc ) ^ beta ) ) ;; desirabilité

      let tmp [0 1]
      set tmp (replace-item 0 tmp cand )
      if ( val != 0 ) [set tmp (replace-item 1 tmp val ) ] ;; si pas de pheromone le lien est très peu desirable

      set choice ( lput tmp choice )
      set i ( i + 1 )
    ]

    set choice (sort-by [ [ l1 l2 ] -> (item 1 l1) > (item 1 l2) ]  choice )

    let next_node 0
    ifelse ( random 1 )  > q0
    [set next_node ( exploration choice )]
    [set next_node ( exploitation choice )]



    set len_cir ( len_cir + ( [len] of ( link ( [who] of cur_node ) next_node ) ) )
    set n_known ( lput next_node n_known )
    set n_left ( remove next_node n_left)

    ;;if (length choice = (length n_all) - 1 )  [show choice] ;; permet d'observer la desirabilité des chemins

    local_update next_node ( [who] of cur_node )
    set cur_node (node next_node)
    move-to cur_node
  ]
end

to-report exploitation[l]
  report ( item 0 (first l) ) ;; la liste est déja triée par desirabilité croissante
end

to-report exploration[l]
  let ttl 0
  foreach l [
    elt ->
    let val ( item 1 elt )
    set ttl ( ttl + val )
  ]
  foreach l [
    elt ->
    let val ( item 1 elt )
    set val ( val / ttl )
  ]
  let rd ( random 1 )
  let _p  0  ;; on somme les valeures de la liste jusqu'à avoir _p>=p, on choisit alors le dernier noeud pour lequel on a sommé
  let i 0
  let n_node ( item 0 ( item 0 l ) ) ;;

  while [_p < rd ] [
    let elt ( item i l )
    set _p ( _p + (item 1 elt) )
    set n_node ( item 0 elt )
    set i ( i + 1 )
    ]

  report n_node
end


to local_update[id_node id_prev_node]
  ask (link id_node id_prev_node) [ ;; evaporation constante
    set phe ( phe - ( p * t0 ) )
    if (phe < 0 ) [ set phe 1 ]
  ]
  ask ( node id_node )[
    let ph_link ( [phe] of ( link id_node id_prev_node ) )

    ;;let incr (max ( [phe] of my-out-links ) )
    ;;set ph_link ( ph_link + p * incr )  ;; formule de Q-learning

    set ph_link ( ph_link + p * t0 )  ;; formule de ACS
  ]
end

to global_update
  ask links[ ;; evaporation constante
    set color grey
    set phe ( phe - ( alpha * t0 ) )
    if (phe < 0 ) [ set phe 1 ]
  ]

  let n_best ( min [len_cir] of ants )
  let best_cir ( one-of ( [n_known ] of ants with [ len_cir = n_best ] ) ) ;; le meilleur circuit de ce tour

  let incr ( 1 / n_best )
  let i 0

  repeat ( ( length best_cir ) - 1 ) [
    let n1 ( item i best_cir )
    let n2 ( item ( i + 1 ) best_cir )

    let ph_l ( [phe] of ( link n1 n2 ) )
    set ph_l ( ph_l + alpha * incr )

    ask ( link n1 n2 ) [ set color red ]
    set i ( i + 1 )
  ]

  ifelse (n_best < 500 )
  [set iter_len n_best]
  [ set iter_len 500] ;; pour éviter que les valeures abhérantes ne rendent le tracé illisible
  ;; on calcule également la condition d'arret
  ifelse ( n_best < cost )
    [ ;; on a amélioré le cout du circuit
     set cost n_best
     set best_circuit best_cir
     set occ 0
    ]
    [  ;; le cout n'a pas changé
     set occ ( occ + 1 )
    ]

  show n_best
  ;;show best_cir

end

to reset_ants
  ask ants[
    ;; cur_node garde sa valeure precedante
    set n_known ( lput ( [who] of cur_node ) [] )
    set len_cir 0
    set n_left (remove ( [who] of cur_node ) n_all )
  ]
end

to reset_global
  reset-ticks
  ask links [ set phe t0 ]
  set cost 10000
  set best_circuit []
  set occ 0
  set nb_it 0
end
@#$#@#$#@
GRAPHICS-WINDOW
210
10
647
448
-1
-1
13.0
1
10
1
1
1
0
1
1
1
-16
16
-16
16
1
1
1
ticks
30.0

BUTTON
23
46
96
79
NIL
setup\n
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
106
84
181
117
NIL
layout
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
20
128
206
161
nb_node
nb_node
0
100
40.0
1
1
NIL
HORIZONTAL

SLIDER
20
174
205
207
nb_ant
nb_ant
0
100
10.0
1
1
NIL
HORIZONTAL

SLIDER
20
231
192
264
beta
beta
0
5
2.0
0.5
1
NIL
HORIZONTAL

SLIDER
21
272
193
305
q0
q0
0
1
0.9
0.1
1
NIL
HORIZONTAL

BUTTON
108
45
174
78
start
go
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
791
119
963
152
p
p
0
1
0.2
0.1
1
NIL
HORIZONTAL

SLIDER
790
187
962
220
gamma
gamma
0
1
0.5
0.1
1
NIL
HORIZONTAL

SLIDER
792
82
964
115
alpha
alpha
0
1
0.1
0.1
1
NIL
HORIZONTAL

SLIDER
793
265
965
298
t0
t0
0
0.01
7.28862973760933E-5
0.0001
1
NIL
HORIZONTAL

SLIDER
792
28
964
61
cond
cond
0
200
100.0
5
1
NIL
HORIZONTAL

PLOT
1046
191
1246
341
cout
NIL
NIL
0.0
100.0
200.0
500.0
true
false
"" ""
PENS
"default" 1.0 0 -2674135 true "" "plot cost"
"pen_iter" 1.0 0 -14070903 true "" "plot iter_len"
"pen-2" 1.0 0 -7500403 true "" "plot heur"

BUTTON
5
84
107
117
NIL
clear_plot
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

@#$#@#$#@
## WHAT IS IT?

(a general understanding of what the model is trying to show or explain)

## HOW IT WORKS

(what rules the agents use to create the overall behavior of the model)

## HOW TO USE IT

(how to use the model, including a description of each of the items in the Interface tab)

## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

(suggested things to add or change in the Code tab to make the model more complicated, detailed, accurate, etc.)

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)

## RELATED MODELS

(models in the NetLogo Models Library and elsewhere which are of related interest)

## CREDITS AND REFERENCES

(a reference to the model's URL on the web if it has one, as well as any other necessary credits, citations, and links)
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.0.3
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
0
@#$#@#$#@
