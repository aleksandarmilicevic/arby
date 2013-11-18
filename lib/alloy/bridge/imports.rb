require 'rjb'
module Alloy
	module Bridge
		module Imports

		Rjb::load('vendor/alloy.jar', ['-Xmx512m', '-Xms256m'])

		A4Reporter_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.A4Reporter')
		CompUtil_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.parser.CompUtil')
		ConstList_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.ConstList')
		Err_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.Err')
		ErrorAPI_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.ErrorAPI')
		SafeList_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.SafeList')
		Command_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.ast.Command')
		SigField_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.ast.Sig$Field')
		Parser_CompModule_RJB= Rjb::import('edu.mit.csail.sdg.alloy4compiler.parser.CompModule')
		A4Options_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4Options')
		A4Solution_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4Solution')
		A4Tuple_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple')
		A4TupleSet_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet')
		TranslateAlloyToKodkod_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod')
		str = Rjb::import('java.lang.String')
		out = Rjb::import('java.lang.System').out
		itr = Rjb::import('java.lang.Iterable')

		end
	end
end