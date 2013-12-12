require 'my_test_helper'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/helpers/test/dsl_sig_test_tmpl'

tmpl = Alloy::Helpers::Test::DslSigTestTmpl.get_test_template('AlloyDslSigTest', 
                                                              'Alloy::Dsl::alloy_model', 
                                                              'sig', 
                                                              'Alloy::Ast::Sig')
eval tmpl

