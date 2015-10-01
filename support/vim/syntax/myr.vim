" Vim Syntax file
" Language: Myrddin
" Maintainer: Ori Bernstein

if exists("b:current_syntax")
    finish
endif

syn region myrComment start=+/\*+ end=+\*/+
syn match myrSpecial display contained "\\\(x\x\+\|\o\{1,3}\|u{.*}\|.\|$\)"
syn match myrFormat display "[^{]{[^}]*}[^}]"
syn region myrString start=+"+ skip=+\\"+ end=+"+ contains=myrSpecial,myrFormat extend
syn region myrChar start=+'+ skip=+\\'+ end=+'+ contains=myrSpecial,myrFormat extend
syn keyword myrKeyword castto
                     \ const
                     \ default
                     \ elif
                     \ else
                     \ export
                     \ extern
                     \ false
                     \ for
                     \ generic
                     \ goto
                     \ if
                     \ match
                     \ pkg
                     \ protect
                     \ sizeof
                     \ struct
                     \ trait
                     \ true
                     \ type
                     \ union
                     \ use
                     \ var
                     \ while

hi def link myrComment  Comment
hi def link myrString   String
hi def link myrChar   String
hi def link myrSpecial  Special
hi def link myrFormat   Special
" Too much color makes my eyes hurt. Just highlight
" the most important and uncommon stuff.
"hi def link myrKeyword  Keyword

let b:current_syntax = "myr"
