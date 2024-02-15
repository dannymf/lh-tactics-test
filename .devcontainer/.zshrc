autoload -U colors && colors
precmd() {
   drawline=""
   for i in {1..$COLUMNS}; do 
      drawline=" $drawline"
   done
   drawline="%U${drawline}%u"
   PS1="%F{252}${drawline}
%B%F{124}%n:%~>%b%f "
}

alias ls="ls --color"

