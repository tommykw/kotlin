/*
 * Copyright 2010-2015 JetBrains s.r.o.
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

package org.jetbrains.kotlin.idea.intentions

import com.intellij.codeInsight.intention.HighPriorityAction
import com.intellij.openapi.editor.Editor
import com.intellij.openapi.util.TextRange
import com.intellij.psi.PsiMember
import com.intellij.psi.PsiModifier
import org.jetbrains.kotlin.descriptors.CallableDescriptor
import org.jetbrains.kotlin.descriptors.DeclarationDescriptorWithVisibility
import org.jetbrains.kotlin.descriptors.Visibilities
import org.jetbrains.kotlin.descriptors.Visibility
import org.jetbrains.kotlin.idea.caches.resolve.resolveToDescriptorIfAny
import org.jetbrains.kotlin.idea.core.canBePrivate
import org.jetbrains.kotlin.idea.core.canBeProtected
import org.jetbrains.kotlin.idea.core.setVisibility
import org.jetbrains.kotlin.idea.core.toDescriptor
import org.jetbrains.kotlin.idea.refactoring.CallableRefactoring
import org.jetbrains.kotlin.idea.refactoring.getAffectedCallables
import org.jetbrains.kotlin.lexer.KtModifierKeywordToken
import org.jetbrains.kotlin.lexer.KtTokens
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi.psiUtil.startOffset
import org.jetbrains.kotlin.psi.psiUtil.visibilityModifier
import java.lang.IllegalArgumentException

open class ChangeVisibilityModifierIntention protected constructor(
        val modifier: KtModifierKeywordToken
) : SelfTargetingRangeIntention<KtDeclaration>(KtDeclaration::class.java, "Make ${modifier.value}") {

    override fun applicabilityRange(element: KtDeclaration): TextRange? {
        val modifierList = element.modifierList
        if (modifierList?.hasModifier(modifier) ?: false) return null

        val descriptor = element.toDescriptor() as? DeclarationDescriptorWithVisibility ?: return null
        val targetVisibility = modifier.toVisibility()
        if (descriptor.visibility == targetVisibility) return null

        if (modifierList?.hasModifier(KtTokens.OVERRIDE_KEYWORD) ?: false) {
            val callableDescriptor = descriptor  as? CallableDescriptor ?: return null
            // cannot make visibility less than (or non-comparable with) any of the supers
            if (callableDescriptor.overriddenDescriptors
                    .map { Visibilities.compare(it.visibility, targetVisibility) }
                    .any { it == null || it > 0  }) return null
        }

        text = defaultText

        val modifierElement = element.visibilityModifier()
        if (modifierElement != null) {
            return modifierElement.textRange
        }

        val defaultRange = noModifierYetApplicabilityRange(element) ?: return null

        if (element is KtPrimaryConstructor && defaultRange.isEmpty) {
            text = "Make primary constructor ${modifier.value}" // otherwise it may be confusing
        }

        return if (modifierList != null)
            TextRange(modifierList.startOffset, defaultRange.endOffset) //TODO: smaller range? now it includes annotations too
        else
            defaultRange
    }

    private val javaVisibilityModifier: String?
        get() = when (modifier) {
            KtTokens.PRIVATE_KEYWORD -> PsiModifier.PRIVATE
            KtTokens.INTERNAL_KEYWORD -> PsiModifier.PACKAGE_LOCAL
            KtTokens.PROTECTED_KEYWORD -> PsiModifier.PROTECTED
            KtTokens.PUBLIC_KEYWORD -> PsiModifier.PUBLIC
            else -> null
        }

    override fun applyTo(element: KtDeclaration, editor: Editor?) {
        val descriptor = (element as? KtNamedDeclaration)?.resolveToDescriptorIfAny() as? CallableDescriptor
                         ?: return element.setVisibility(modifier)

        object : CallableRefactoring<CallableDescriptor>(element.project, descriptor, text) {
            override fun performRefactoring(descriptorsForChange: Collection<CallableDescriptor>) {
                val callables = getAffectedCallables(project, descriptorsForChange)
                for (callable in callables) {
                    when (callable) {
                        is KtModifierListOwner -> callable.setVisibility(modifier)
                        is PsiMember -> javaVisibilityModifier?.let { callable.modifierList?.setModifierProperty(it, true) }
                    }
                }
            }
        }.run()
    }

    private fun KtModifierKeywordToken.toVisibility(): Visibility {
        return when (this) {
            KtTokens.PUBLIC_KEYWORD -> Visibilities.PUBLIC
            KtTokens.PRIVATE_KEYWORD -> Visibilities.PRIVATE
            KtTokens.PROTECTED_KEYWORD -> Visibilities.PROTECTED
            KtTokens.INTERNAL_KEYWORD -> Visibilities.INTERNAL
            else -> throw IllegalArgumentException("Unknown visibility modifier:$this")
        }
    }

    private fun noModifierYetApplicabilityRange(declaration: KtDeclaration): TextRange? {
        if (KtPsiUtil.isLocal(declaration)) return null
        return when (declaration) {
            is KtNamedFunction -> declaration.funKeyword?.textRange
            is KtProperty -> declaration.valOrVarKeyword.textRange
            is KtClass -> declaration.getClassOrInterfaceKeyword()?.textRange
            is KtObjectDeclaration -> declaration.getObjectKeyword()?.textRange
            is KtPrimaryConstructor -> declaration.valueParameterList?.let { TextRange.from(it.startOffset, 0) } //TODO: use constructor keyword if exist
            is KtSecondaryConstructor -> declaration.getConstructorKeyword().textRange
            is KtParameter -> declaration.valOrVarKeyword?.textRange
            is KtTypeAlias -> declaration.getTypeAliasKeyword()?.textRange
            else -> null
        }
    }

    class Public : ChangeVisibilityModifierIntention(KtTokens.PUBLIC_KEYWORD), HighPriorityAction

    class Private : ChangeVisibilityModifierIntention(KtTokens.PRIVATE_KEYWORD), HighPriorityAction {
        override fun applicabilityRange(element: KtDeclaration): TextRange? {
            return if (element.canBePrivate()) super.applicabilityRange(element) else null
        }
    }

    class Protected : ChangeVisibilityModifierIntention(KtTokens.PROTECTED_KEYWORD) {
        override fun applicabilityRange(element: KtDeclaration): TextRange? {
            return if (element.canBeProtected()) super.applicabilityRange(element) else null
        }
    }

    class Internal : ChangeVisibilityModifierIntention(KtTokens.INTERNAL_KEYWORD)
}
