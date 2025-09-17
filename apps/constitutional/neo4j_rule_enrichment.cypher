MERGE (ru:Rule {id:'R0'})
SET ru.name = coalesce(ru.name,'NoIrreversibleActionWithoutReview'),
    ru.version = coalesce(ru.version,'1'),
    ru.requires_review_for_irreversible = true,
    ru.priority = 'DENY_PRECEDENCE';
