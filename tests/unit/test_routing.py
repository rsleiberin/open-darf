from apps.document_processor.routing import decide_processor


def test_routing_lambda_default_threshold():
    assert decide_processor(10) == "lambda"


def test_routing_ec2_default_threshold():
    assert decide_processor(100.01) == "ec2"
