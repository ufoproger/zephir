/*
 * This file is part of the Zephir.
 *
 * (c) Phalcon Team <team@zephir-lang.com>
 *
 * For the full copyright and license information, please view the LICENSE
 * file that was distributed with this source code. If you did not receive
 * a copy of the license it is available through the world-wide-web at the
 * following url: https://docs.zephir-lang.com/en/latest/license
 */

#include <php.h>
#include "php_ext.h"

#include <Zend/zend_API.h>
#include <Zend/zend_exceptions.h>
#include <Zend/zend_execute.h>

#include "kernel/main.h"
#include "kernel/fcall.h"
#include "kernel/memory.h"
#include "kernel/string.h"
#include "kernel/operators.h"
#include "kernel/exception.h"
#include "kernel/backtrace.h"
#include "kernel/variables.h"

int zephir_has_constructor_ce(const zend_class_entry *ce)
{
	do {
		if (ce->constructor != NULL) {
			return 1;
		}

		ce = ce->parent;
	} while (ce);

	return 0;
}

/**
 * Creates a unique key to cache the current method/function call address for the current scope
 */
static int zephir_make_fcall_key(zend_string* s, zephir_call_type type, zend_class_entry *ce, zval *function, const zend_class_entry* called_scope)
{
	const zend_class_entry *calling_scope;
	unsigned char t;

#if PHP_VERSION_ID >= 70100
	calling_scope = zend_get_executed_scope();
#else
	calling_scope = EG(scope);
#endif

	switch (type) {
		case zephir_fcall_parent:
			if (UNEXPECTED(!calling_scope || !calling_scope->parent)) {
				return FAILURE;
			}

			calling_scope = calling_scope->parent;
			break;

		case zephir_fcall_static:
			calling_scope = called_scope;
			if (UNEXPECTED(!calling_scope)) {
				return FAILURE;
			}

			break;

		case zephir_fcall_self:
			/* EG(scope) */
			break;

		case zephir_fcall_function:
			if (Z_TYPE_P(function) == IS_OBJECT) {
				return FAILURE;
			}

			calling_scope = NULL;
			called_scope  = NULL;
			break;

		case zephir_fcall_ce:
			calling_scope = ce;
			called_scope  = ce;
			break;

		case zephir_fcall_method:
			if (Z_TYPE_P(function) == IS_OBJECT) {
				return FAILURE;
			}

			calling_scope = ce;
			called_scope  = ce;
			break;

		default:
			return FAILURE;
	}

	if (called_scope == calling_scope) {
	/* Calls within the same scope, this won't trigger magic methods or failures due to restricted visibility */
		t = 0;
	}
	else if (called_scope && calling_scope && (instanceof_function(called_scope, calling_scope) || instanceof_function(calling_scope, called_scope))) {
	/* Calls within the same chain of inheritance; can call protected methods */
		t = 1;
	}
	else {
	/* Can safely call only public methods */
		t = 2;
	}

	{
		char* cls      = calling_scope ? ZSTR_VAL(calling_scope->name) : "";
		size_t cls_len = calling_scope ? ZSTR_LEN(calling_scope->name) : 0;
		char* mth      = NULL;
		size_t mth_len = 0;
		char* buf;

		if (Z_TYPE_P(function) == IS_STRING) {
			mth     = Z_STRVAL_P(function);
			mth_len = Z_STRLEN_P(function);
		}
		else if (Z_TYPE_P(function) == IS_ARRAY) {
			zval *method;
			HashTable *function_hash = Z_ARRVAL_P(function);
			if (
					function_hash->nNumOfElements == 2
				 && ((method = zend_hash_index_find(function_hash, 1)) != NULL)
				 && Z_TYPE_P(method) == IS_STRING
			) {
				mth     = Z_STRVAL_P(method);
				mth_len = Z_STRLEN_P(method);
			}
		}

		if (cls_len + 1 + mth_len + sizeof(unsigned char) > 255) {
			return FAILURE;
		}

		ZSTR_LEN(s) = cls_len + 1 + mth_len + sizeof(unsigned char);
		buf = ZSTR_VAL(s);
		zend_str_tolower_copy(buf, cls, cls_len + 1);
		zend_str_tolower_copy(buf + cls_len + 1, mth, mth_len);
		buf[cls_len + 1 + mth_len] = t;
		buf[cls_len + 1 + mth_len + sizeof(t)] = '\0';
	}

	ZSTR_H(s) = zend_hash_func(ZSTR_VAL(s), ZSTR_LEN(s));
	return SUCCESS;
}

static void resolve_callable(zval* retval, zephir_call_type type, zend_class_entry *ce, zval *object, zval *function)
{
	if (type == zephir_fcall_function || IS_ARRAY == Z_TYPE_P(function) || IS_OBJECT == Z_TYPE_P(function)) {
		ZVAL_COPY(retval, function);
		return;
	}

	array_init_size(retval, 2);
	zend_hash_real_init(Z_ARRVAL_P(retval), 1);
	ZEND_HASH_FILL_PACKED(Z_ARRVAL_P(retval)) {
		zval q;
		switch (type) {
			case zephir_fcall_parent:
				zend_string_addref(i_parent);
				ZVAL_STR(&q, i_parent);
				ZEND_HASH_FILL_ADD(&q);
				break;

			case zephir_fcall_self:
				zend_string_addref(i_self);
				ZVAL_STR(&q, i_self);
				ZEND_HASH_FILL_ADD(&q);
				break;

			case zephir_fcall_static:
				zend_string_addref(i_static);
				ZVAL_STR(&q, i_static);
				ZEND_HASH_FILL_ADD(&q);
				break;

			case zephir_fcall_ce:
				assert(ce);
				zend_string_addref(ce->name);
				ZVAL_STR(&q, ce->name);
				ZEND_HASH_FILL_ADD(&q);
				break;

			default:
				assert(object);
				Z_TRY_ADDREF_P(object);
				ZEND_HASH_FILL_ADD(object);
				break;
		}

		Z_TRY_ADDREF_P(function);
		ZEND_HASH_FILL_ADD(function);
	} ZEND_HASH_FILL_END();
}

static void populate_fcic(zend_fcall_info_cache* fcic, zephir_call_type type, zend_class_entry* ce, zval *this_ptr, zval *func, zend_class_entry* called_scope)
{
	zend_class_entry* calling_scope;

#if PHP_VERSION_ID < 70300
	fcic->initialized      = 0;
#endif
	fcic->function_handler = NULL;

	if (type == zephir_fcall_function && Z_TYPE_P(func) == IS_STRING) {
#if PHP_VERSION_ID < 70300
		fcic->initialized   = 1;
#endif
		fcic->called_scope  = NULL;
		fcic->calling_scope = NULL;
		fcic->object        = NULL;
		return;
	}

	fcic->called_scope = called_scope;

#if PHP_VERSION_ID >= 70100
	calling_scope = zend_get_executed_scope();
#else
	calling_scope = EG(scope);
#endif

	fcic->object = this_ptr ? Z_OBJ_P(this_ptr) : NULL;
	switch (type) {
		case zephir_fcall_parent:
			if (UNEXPECTED(!calling_scope || !calling_scope->parent)) {
				return;
			}

			fcic->calling_scope = calling_scope->parent;
			break;

		case zephir_fcall_static:
			fcic->calling_scope = fcic->called_scope;
			if (UNEXPECTED(!calling_scope)) {
				return;
			}

			break;

		case zephir_fcall_self:
			fcic->calling_scope = calling_scope;
			break;

		case zephir_fcall_ce:
			fcic->calling_scope = ce;
			fcic->called_scope  = ce;
			break;

		case zephir_fcall_function:
		case zephir_fcall_method:
			if (Z_TYPE_P(func) == IS_OBJECT) {
#if PHP_VERSION_ID >= 80000
				if (Z_OBJ_HANDLER_P(func, get_closure) && Z_OBJ_HANDLER_P(func, get_closure)(Z_OBJ_P(func), &fcic->calling_scope, &fcic->function_handler, &fcic->object, 0) == SUCCESS) {
#else
				if (Z_OBJ_HANDLER_P(func, get_closure) && Z_OBJ_HANDLER_P(func, get_closure)(func, &fcic->calling_scope, &fcic->function_handler, &fcic->object) == SUCCESS) {
#endif
					fcic->called_scope = fcic->calling_scope;
					break;
				}

				return;
			}

			fcic->calling_scope = this_ptr ? Z_OBJCE_P(this_ptr) : NULL;
			fcic->called_scope  = fcic->calling_scope;
			break;

		default:
			return;
	}

#if PHP_VERSION_ID < 70300
	fcic->initialized = 1;
#endif
}

/**
 * Calls a function/method in the PHP userland
 */
int zephir_call_func_aparams(zval *return_value_ptr, const char *func_name, uint32_t func_length,
	zephir_fcall_cache_entry **cache_entry, int cache_slot,
	uint32_t param_count, zval **params)
{
	return dao_call_method_with_params(return_value_ptr, NULL, NULL, zephir_fcall_function, func_name, func_length, param_count, params);
}

int zephir_call_zval_func_aparams(zval *return_value_ptr, zval *func_name,
	zephir_fcall_cache_entry **cache_entry, int cache_slot,
	uint32_t param_count, zval **params)
{
	return dao_call_user_func_params(return_value_ptr, func_name, param_count, params);
}

int zephir_call_class_method_aparams(zval *return_value, zend_class_entry *ce, zephir_call_type type, zval *object,
	const char *method_name, uint32_t method_len,
	zephir_fcall_cache_entry **cache_entry, int cache_slot,
	uint32_t param_count, zval **params)
{
	return dao_call_method_with_params(return_value, object, ce, type, method_name, method_len, param_count, params);
}

/**
 * Replaces call_user_func_array avoiding function lookup
 * This function does not return FAILURE if an exception has ocurred
 */
int zephir_call_user_func_array_noex(zval *return_value, zval *handler, zval *params)
{
	return dao_call_user_func_array_noex(return_value, handler, params);
}

/**
 * If a retval_ptr is specified, PHP's implementation of zend_eval_stringl
 * simply prepends a "return " which causes only the first statement to be executed
 */
void zephir_eval_php(zval *str, zval *retval_ptr, char *context)
{
	zval local_retval;
	zend_op_array *new_op_array = NULL;
	uint32_t original_compiler_options;

	ZVAL_UNDEF(&local_retval);

	original_compiler_options = CG(compiler_options);
	CG(compiler_options) = ZEND_COMPILE_DEFAULT_FOR_EVAL;
	new_op_array = zend_compile_string(str, context);
	CG(compiler_options) = original_compiler_options;

	if (new_op_array)
	{
		EG(no_extensions) = 1;
		zend_try {
			zend_execute(new_op_array, &local_retval);
		} zend_catch {
			destroy_op_array(new_op_array);
			efree_size(new_op_array, sizeof(zend_op_array));
			zend_bailout();
		} zend_end_try();
		EG(no_extensions) = 0;

		if (Z_TYPE(local_retval) != IS_UNDEF) {
			if (retval_ptr) {
				ZVAL_COPY_VALUE(retval_ptr, &local_retval);
			} else {
				zval_ptr_dtor(&local_retval);
			}
		} else if (retval_ptr) {
			ZVAL_NULL(retval_ptr);
		}

		destroy_op_array(new_op_array);
		efree_size(new_op_array, sizeof(zend_op_array));
	}
}

/**
 * Functions from Dao framework.
 */
static zend_never_inline zend_function *dao_get_function(zend_class_entry *scope, zend_string *function_name)
{
	zval *func;
	zend_function *fbc;

	func = zend_hash_find(&scope->function_table, function_name);
	if (func != NULL) {
		fbc = Z_FUNC_P(func);
		return fbc;
	}

	return NULL;
}

static zend_result dao_call_user_function(zend_function *fn, zend_class_entry *called_scope, zval *object, zval *function_name, zval *retval_ptr, uint32_t param_count, zval params[])
{
	zend_fcall_info fci;
	zend_fcall_info_cache fcic;

	fci.size = sizeof(fci);
	fci.object = object ? Z_OBJ_P(object) : NULL;
	ZVAL_COPY_VALUE(&fci.function_name, function_name);
	fci.retval = retval_ptr;
	fci.param_count = param_count;
	fci.params = params;

	fci.named_params = NULL;

	if (fn != NULL) {
		fcic.function_handler = fn;
		fcic.object = object ? Z_OBJ_P(object) : NULL;
		fcic.called_scope = called_scope;

		return zend_call_function(&fci, &fcic);
	}
	return zend_call_function(&fci, NULL);
}

int dao_call_method_with_params(zval *retval, zval *object, zend_class_entry *ce, zephir_call_type type, const char *method_name, uint method_len, uint param_count, zval *params[])
{
	zval func_name = {}, ret = {}, *retval_ptr = (retval != NULL) ? retval : &ret, obj = {};
	zval *arguments;
	zend_function *fbc = NULL;

	int i, status;

	if (type != zephir_fcall_function) {
		if (type != zephir_fcall_ce && type != zephir_fcall_self && type != zephir_fcall_static) {
			if (object == NULL || Z_TYPE_P(object) != IS_OBJECT) {
				zephir_throw_exception_format(spl_ce_RuntimeException, "Trying to call method %s on a non-object", method_name);
				return FAILURE;
			}
		}

		if (object == NULL || Z_TYPE_P(object) != IS_OBJECT) {
			if (zend_get_this_object(EG(current_execute_data))){
				ZVAL_OBJ(&obj, zend_get_this_object(EG(current_execute_data)));
				object = &obj;
			}
		}

		if (!ce && object && Z_TYPE_P(object) == IS_OBJECT) {
			ce = Z_OBJCE_P(object);
		}
		assert(ce != NULL);

		zend_string *str_methodname = zend_string_init(method_name, method_len, 0);
		if (type != zephir_fcall_parent) {
			fbc = dao_get_function(ce, str_methodname);
		} else {
			fbc = dao_get_function(ce->parent, str_methodname);
		}
		if (fbc) {
			ZVAL_STR(&func_name, str_methodname);
		} else {
			zend_string_release(str_methodname);

			switch (type) {
				case zephir_fcall_ce:
					array_init_size(&func_name, 2);
					add_next_index_string(&func_name, ce->name->val);
					add_next_index_stringl(&func_name, method_name, method_len);
					break;
				case zephir_fcall_parent:
					if (dao_memnstr_str_str(method_name, method_len, "::", 2)) {
						dao_fast_explode_str_str(&func_name, "::", 2, method_name, method_len);
					} else {
						array_init_size(&func_name, 2);
						add_next_index_stringl(&func_name, "parent", 6);
						add_next_index_stringl(&func_name, method_name, method_len);
					}
					break;
				case zephir_fcall_self:
					assert(ce != NULL);
					array_init_size(&func_name, 2);
					add_next_index_stringl(&func_name, "self", 4);
					add_next_index_stringl(&func_name, method_name, method_len);
					break;
				case zephir_fcall_method:
					array_init_size(&func_name, 2);
					Z_TRY_ADDREF_P(object);
					add_next_index_zval(&func_name, object);
					add_next_index_stringl(&func_name, method_name, method_len);
					break;
				default:
					zephir_throw_exception_format(spl_ce_RuntimeException, "Error call type %d for method %s", type, method_name);
					return FAILURE;
			}
		}
	} else {
		ZVAL_STRINGL(&func_name, method_name, method_len);
	}

	arguments = param_count ? safe_emalloc(sizeof(zval), param_count, 0) : NULL;

	i = 0;
	while(i < param_count) {
		if (params[i] && Z_TYPE_P(params[i]) > IS_NULL) {
			ZVAL_COPY_VALUE(&arguments[i], params[i]);
		} else {
			ZVAL_NULL(&arguments[i]);
		}
		i++;
	}

	if (
		(status = dao_call_user_function(fbc, ce, object, &func_name, retval_ptr, param_count, arguments)) == FAILURE || EG(exception)
	) {
		status = FAILURE;
		ZVAL_NULL(retval_ptr);
		if (!EG(exception)) {
			switch (type) {
				case zephir_fcall_function:
					zend_error(E_ERROR, "Call to undefined function %s()", method_name);
					break;
				case zephir_fcall_parent:
					zend_error(E_ERROR, "Call to undefined method parent::%s()", method_name);
					break;
				case zephir_fcall_self:
					zend_error(E_ERROR, "Call to undefined method self::%s()", method_name);
					break;
				case zephir_fcall_static:
					zend_error(E_ERROR, "Call to undefined function static::%s()", method_name);
					break;
				case zephir_fcall_ce:
					zend_error(E_ERROR, "Call to undefined method %s::%s()", ce->name->val, method_name);
					break;
				case zephir_fcall_method:
					zend_error(E_ERROR, "Call to undefined method %s::%s()", Z_OBJCE_P(object)->name->val, method_name);
					break;
				default:
					zend_error(E_ERROR, "Call to undefined method ?::%s()", method_name);
			}
		}
	}
	zval_ptr_dtor(&func_name);
	efree(arguments);
	if (retval == NULL) {
		if (!Z_ISUNDEF(ret)) {
			zval_ptr_dtor(&ret);
		}
	}

	return status;
}

int dao_call_user_func_params(zval *retval, zval *handler, int param_count, zval *params[])
{
	zval ret = {}, *retval_ptr = (retval != NULL) ? retval : &ret;
	zval *arguments;
	int i, status;

	arguments = param_count ? safe_emalloc(sizeof(zval), param_count, 0) : NULL;

	i = 0;
	while(i < param_count) {
		if (params[i]) {
			ZVAL_COPY_VALUE(&arguments[i], params[i]);
		} else {
			ZVAL_NULL(&arguments[i]);
		}
		i++;
	}

#if PHP_VERSION_ID >= 70100
	if ((status = call_user_function(NULL, NULL, handler, retval_ptr, param_count, arguments)) == FAILURE || EG(exception)) {
		status = FAILURE;
		ZVAL_NULL(retval_ptr);
	}
#else
	if ((status = call_user_function(EG(function_table), NULL, handler, retval_ptr, param_count, arguments)) == FAILURE || EG(exception)) {
		status = FAILURE;
		ZVAL_NULL(retval_ptr);
	}
#endif

	efree(arguments);

	return status;
}

int dao_call_user_func_array(zval *retval, zval *handler, zval *params)
{
	zval ret = {}, *retval_ptr = (retval != NULL) ? retval : &ret, *arguments = NULL, *param;
	int params_count = 0, i, status;

	if (params && Z_TYPE_P(params) != IS_ARRAY && Z_TYPE_P(params) > IS_NULL) {
		status = FAILURE;
		php_error_docref(NULL, E_WARNING, "Invalid arguments supplied for dao_call_user_func_array()");
		return status;
	}

	if (params && Z_TYPE_P(params) == IS_ARRAY) {
		params_count = zend_hash_num_elements(Z_ARRVAL_P(params));
		arguments = (zval*)emalloc(sizeof(zval) * params_count);
		i = 0;
		ZEND_HASH_FOREACH_VAL(Z_ARRVAL_P(params), param) {
			ZVAL_COPY_VALUE(&arguments[i], param);
			i++;
		} ZEND_HASH_FOREACH_END();
	} else {
		params_count = 0;
		arguments = NULL;
	}

#if PHP_VERSION_ID >= 70100
	if ((status = call_user_function(NULL, NULL, handler, retval_ptr, params_count, arguments)) == FAILURE || EG(exception)) {
		status = FAILURE;
		ZVAL_NULL(retval_ptr);
	}
#else
	if ((status = call_user_function(EG(function_table), NULL, handler, retval_ptr, params_count, arguments)) == FAILURE || EG(exception)) {
		status = FAILURE;
		ZVAL_NULL(retval_ptr);
	}
#endif

	efree(arguments);

	return status;
}
