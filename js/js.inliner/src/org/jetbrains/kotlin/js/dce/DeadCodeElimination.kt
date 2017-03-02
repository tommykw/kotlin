/*
 * Copyright 2010-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.jetbrains.kotlin.js.dce

import org.jetbrains.kotlin.js.backend.ast.*
import java.util.*

class DeadCodeElimination(private val root: JsStatement) {
    val nodes = mutableMapOf<JsName, Node>()
    val dynamicNode = Node(null)
    val worklist: Queue<() -> Unit> = ArrayDeque()
    val processedFunctions = mutableSetOf<JsFunction>()

    fun apply() {
        root.accept(visitor)
        while (worklist.isNotEmpty()) {
            worklist.remove()()
        }
    }

    val visitor = object : RecursiveJsVisitor() {
        var resultNodes: List<Node> = listOf()

        override fun visitBinaryExpression(x: JsBinaryOperation) {
            if (x.operator == JsBinaryOperator.ASG) {
                x.arg1.accept(this)
                val lhsNodes = resultNodes
                x.arg2.accept(this)
                val rhsNodes = resultNodes
                for (lhsNode in lhsNodes) {
                    for (rhsNode in rhsNodes) {
                        rhsNode.connectTo(lhsNode)
                    }
                }
            }
            else if (x.operator == JsBinaryOperator.OR) {
                x.arg1.accept(this)
                val first = resultNodes
                x.arg2.accept(this)
                val second = resultNodes
                resultNodes = first + second
            }
            else {
                super.visitBinaryExpression(x)
            }
        }

        override fun visitFunction(x: JsFunction) {
            val node = Node(x)
            x.name?.let {
                nodes[it] = node
            }
            node.addFunction(x)
            resultNodes = listOf(node)
        }

        override fun visitObjectLiteral(x: JsObjectLiteral) {
            val node = Node(x)
            for (propertyInitializer in x.propertyInitializers) {
                propertyInitializer.valueExpr.accept(this)
                val propertyNodes = resultNodes
                val label = propertyInitializer.labelExpr
                when (label) {
                    is JsNameRef -> {
                        propertyNodes.forEach { it.connectTo(node.getMember(label.ident)) }
                    }
                    is JsStringLiteral -> {
                        propertyNodes.forEach { it.connectTo(node.getMember(label.value)) }
                    }
                    else -> {
                        propertyNodes.forEach { it.connectTo(node.getDynamicMember()) }
                    }
                }
            }
            resultNodes = listOf(node)
        }

        override fun visit(x: JsVars.JsVar) {
            val node = Node(x)
            nodes[x.name] = node
            x.initExpression?.let {
                accept(it)
            }
            resultNodes = listOf()
        }

        override fun visitNameRef(nameRef: JsNameRef) {
            val qualifier = nameRef.qualifier
            resultNodes = if (qualifier == null) {
                val name = nameRef.name
                listOf(name?.let { nodes[it] } ?: dynamicNode)
            }
            else {
                accept(qualifier)
                resultNodes.map { it.getMember(nameRef.ident) }
            }
        }

        override fun visitArrayAccess(x: JsArrayAccess) {
            accept(x.arrayExpression)
            val arrayNodes = resultNodes

            val indexExpr = x.indexExpression
            resultNodes = if (indexExpr is JsStringLiteral) {
                arrayNodes.map { it.getMember(indexExpr.value) }
            }
            else {
                arrayNodes.map { it.getDynamicMember() }
            }
        }
    }

    inner class Node(val jsNode: JsNode?) {
        private var functions: MutableSet<JsFunction>? = null
        private var members: MutableMap<String, Node>? = null
        private var dynamicMemberImpl: Node? = null
        private var parameters: MutableList<Node?>? = null
        private var returnValueImpl: Node? = null
        private var handlers: MutableList<NodeEventHandler>? = null
        private var successors: MutableSet<Node>? = null

        fun getFunctions(): Set<JsFunction> = functions ?: emptySet()

        fun addFunction(function: JsFunction) {
            val set = functions ?: mutableSetOf<JsFunction>().also { functions = it }
            if (set.add(function)) {
                worklist += { handlers?.forEach { it.functionAdded(function) } }
            }
        }

        fun getKeys(): Set<String> = members?.keys.orEmpty()

        fun getMemberIfPossible(name: String): Node? = members?.get(name)

        fun getMember(name: String): Node {
            return members?.get(name) ?: Node(null).also {
                val members = this.members ?: mutableMapOf<String, Node>().also { this.members = it }
                members.getOrPut(name) {
                    Node(null).also { newNode ->
                        worklist += { handlers?.forEach { it.memberAdded(name, newNode) } }
                    }
                }
            }
        }

        fun getDynamicMemberIfPossible(): Node? = dynamicMemberImpl

        fun getDynamicMember(): Node {
            return dynamicMemberImpl ?: Node(null).also { newNode ->
                dynamicMemberImpl = newNode
                worklist += { handlers?.forEach { it.dynamicMemberAdded(newNode) } }
                addHandler(object : NodeEventHandler {
                    override fun memberAdded(name: String, value: Node) {
                        newNode.connectTo(value)
                        value.connectTo(newNode)
                    }
                })
            }
        }

        fun getParameterIfPossible(index: Int): Node? = parameters?.getOrNull(index)

        fun getParameterCount() = parameters?.size ?: 0

        fun getParameter(index: Int): Node {
            val list = parameters ?: mutableListOf<Node?>().also { parameters = it }
            while (list.lastIndex < index) {
                list.add(null)
            }
            return list[index] ?: Node(null).also { param ->
                list[index] = param
                worklist += { handlers?.forEach { it.parameterAdded(index, param) } }
            }
        }

        fun getReturnValueIfPossible(): Node? = returnValueImpl

        fun getReturnValue(): Node {
            return returnValueImpl ?: Node(null).also { newReturnValue ->
                returnValueImpl = newReturnValue
                worklist += { handlers?.forEach { it.returnValueAdded(newReturnValue) } }
            }
        }

        fun connectTo(other: Node) {
            val successors = this.successors ?: mutableSetOf<Node>().also { this.successors = it }
            if (successors.add(other)) {
                addHandler(object : NodeEventHandler {
                    override fun functionAdded(function: JsFunction) {
                        other.addFunction(function)
                    }

                    override fun parameterAdded(index: Int, value: Node) {
                        value.connectTo(other.getParameter(index))
                    }

                    override fun returnValueAdded(value: Node) {
                        getReturnValue().connectTo(value)
                    }

                    override fun dynamicMemberAdded(value: Node) {
                        other.getDynamicMember().connectTo(value)
                        value.connectTo(other.getDynamicMember())
                    }

                    override fun memberAdded(name: String, value: Node) {
                        value.connectTo(other.getMember(name))
                        other.getMember(name).connectTo(value)
                    }
                })
            }
            other.addHandler(object : NodeEventHandler {
                override fun returnValueAdded(value: Node) {
                    value.connectTo(getReturnValue())
                }

                override fun dynamicMemberAdded(value: Node) {
                    getDynamicMember().connectTo(value)
                    value.connectTo(getDynamicMember())
                }

                override fun memberAdded(name: String, value: Node) {
                    value.connectTo(getMember(name))
                    getMember(name).connectTo(value)
                }
            })
        }

        fun addHandler(handler: NodeEventHandler) {
            val list = handlers ?: mutableListOf<NodeEventHandler>().also { handlers = it }
            list += handler

            functions?.forEach { function ->
                worklist += { handler.functionAdded(function) }
            }

            dynamicMemberImpl?.let { dynamicMember ->
                worklist += { handler.dynamicMemberAdded(dynamicMember) }
            }

            members?.let {
                for ((name, value) in it) {
                    worklist += { handler.memberAdded(name, value) }
                }
            }

            parameters?.let {
                for ((index, param) in it.withIndex()) {
                    if (param != null) {
                        worklist += { handler.parameterAdded(index, param) }
                    }
                }
            }

            returnValueImpl?.let {
                worklist += { handler.returnValueAdded(it) }
            }
        }
    }

    interface NodeEventHandler {
        fun functionAdded(function: JsFunction) {}

        fun parameterAdded(index: Int, value: Node) {}

        fun returnValueAdded(value: Node) {}

        fun dynamicMemberAdded(value: Node) {}

        fun memberAdded(name: String, value: Node) {}
    }
}