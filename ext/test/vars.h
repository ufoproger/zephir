
extern zend_class_entry *test_vars_ce;

ZEPHIR_INIT_CLASS(Test_Vars);

PHP_METHOD(Test_Vars, testVarDump);
PHP_METHOD(Test_Vars, testVarExport);
PHP_METHOD(Test_Vars, test88Issue);
PHP_METHOD(Test_Vars, test88IssueParam2InitString);

ZEND_BEGIN_ARG_INFO_EX(arginfo_test_vars_test88issue, 0, 0, 1)
	ZEND_ARG_INFO(0, param1)
	ZEND_ARG_INFO(0, param2)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_test_vars_test88issueparam2initstring, 0, 0, 1)
	ZEND_ARG_INFO(0, param1)
	ZEND_ARG_INFO(0, param2)
ZEND_END_ARG_INFO()

ZEPHIR_INIT_FUNCS(test_vars_method_entry) {
	PHP_ME(Test_Vars, testVarDump, NULL, ZEND_ACC_PUBLIC)
	PHP_ME(Test_Vars, testVarExport, NULL, ZEND_ACC_PUBLIC)
	PHP_ME(Test_Vars, test88Issue, arginfo_test_vars_test88issue, ZEND_ACC_PUBLIC)
	PHP_ME(Test_Vars, test88IssueParam2InitString, arginfo_test_vars_test88issueparam2initstring, ZEND_ACC_PUBLIC)
	PHP_FE_END
};