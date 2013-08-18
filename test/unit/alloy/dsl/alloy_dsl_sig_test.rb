require 'unit/alloy/alloy_test_helper.rb'
require_relative 'alloy_dsl_sig_test_tmpl.rb'

tmpl = get_test_template('AlloyDslSigTest', 'Alloy::Dsl::alloy_model', 'Alloy::Dsl::ModelDslApi.sig', 'Alloy::Ast::Sig')
eval tmpl

