
extern zend_class_entry *stub_properties_staticprivateproperties_ce;

ZEPHIR_INIT_CLASS(Stub_Properties_StaticPrivateProperties);

PHP_METHOD(Stub_Properties_StaticPrivateProperties, getInstance);

ZEND_BEGIN_ARG_WITH_RETURN_OBJ_INFO_EX(arginfo_stub_properties_staticprivateproperties_getinstance, 0, 0, Stub\\Properties\\StaticPrivateProperties, 0)
ZEND_END_ARG_INFO()

ZEPHIR_INIT_FUNCS(stub_properties_staticprivateproperties_method_entry) {
	PHP_ME(Stub_Properties_StaticPrivateProperties, getInstance, arginfo_stub_properties_staticprivateproperties_getinstance, ZEND_ACC_PUBLIC|ZEND_ACC_STATIC)
	PHP_FE_END
};
