<?php

/*
 * This file is part of the Zephir.
 *
 * (c) Zephir Team <team@zephir-lang.com>
 *
 * For the full copyright and license information, please view the LICENSE
 * file that was distributed with this source code.
 */

namespace Zephir\Optimizers\FunctionCall;

use Zephir\Call;
use Zephir\CompilationContext;
use Zephir\CompiledExpression;
use Zephir\Exception\CompilerException;
use Zephir\Optimizers\OptimizerAbstract;

/**
 * PrepareVirtualPathOptimizer
 *
 * Optimizes calls to 'prepare_virtual_path' using internal function
 */
class PrepareVirtualPathOptimizer extends OptimizerAbstract
{
    /**
     * @param  array                         $expression
     * @param  Call                          $call
     * @param  CompilationContext            $context
     * @throws CompilerException
     * @return bool|CompiledExpression|mixed
     */
    public function optimize(array $expression, Call $call, CompilationContext $context)
    {
        if (!isset($expression['parameters'])) {
            return false;
        }

        if (count($expression['parameters']) != 2) {
            return false;
        }

        $context->headersManager->add('kernel/file');

        /**
         * Process the expected symbol to be returned
         */
        $call->processExpectedReturn($context);

        $symbolVariable = $call->getSymbolVariable(true, $context);

        if ($symbolVariable->isNotVariableAndString()) {
            throw new CompilerException('Returned values by functions can only be assigned to variant variables', $expression);
        }

        $resolvedParams = $call->getReadOnlyResolvedParams($expression['parameters'], $context, $expression);

        if ($call->mustInitSymbolVariable()) {
            $symbolVariable->initVariant($context);
        }

        $symbol = $context->backend->getVariableCode($symbolVariable);
        $context->codePrinter->output('zephir_prepare_virtual_path(' . $symbol . ', ' . $resolvedParams[0] . ', ' . $resolvedParams[1] . ' TSRMLS_CC);');

        return new CompiledExpression('variable', $symbolVariable->getRealName(), $expression);
    }
}
