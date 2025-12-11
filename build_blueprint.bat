

lake build BV :blueprint
@REM this posts build failures I don't understand
@REM py -m leanblueprint.client all
py -m leanblueprint.client pdf
py -m leanblueprint.client web
py -m leanblueprint.client serve