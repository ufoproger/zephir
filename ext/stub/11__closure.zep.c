
#ifdef HAVE_CONFIG_H
#include "../ext_config.h"
#endif

#include <php.h>
#include "../php_ext.h"
#include "../ext.h"

#include <Zend/zend_operators.h>
#include <Zend/zend_exceptions.h>
#include <Zend/zend_interfaces.h>

#include "kernel/main.h"
#include "kernel/object.h"


ZEPHIR_INIT_CLASS(stub_11__closure) {

	ZEPHIR_REGISTER_CLASS(stub, 11__closure, stub, 11__closure, stub_11__closure_method_entry, ZEND_ACC_FINAL_CLASS);

	return SUCCESS;

}

PHP_METHOD(stub_11__closure, __invoke) {

	zval *this_ptr = getThis();



	RETURN_LONG(5);

}

