package graphics

import (
	"bytes"
	"errors"
	"fmt"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	chart "github.com/wcharczuk/go-chart"
)

func listToPoint(expr expreduceapi.Ex) (float64, float64, error) {
	list, isList := atoms.HeadAssertion(expr, "System`List")
	if !isList {
		return 0, 0, fmt.Errorf("expected point to be list")
	}
	if list.Len() != 2 {
		return 0, 0, fmt.Errorf("points should be of length 2")
	}
	xFlt, xIsFlt := list.GetPart(1).(*atoms.Flt)
	yFlt, yIsFlt := list.GetPart(2).(*atoms.Flt)
	if !xIsFlt || !yIsFlt {
		return 0, 0, fmt.Errorf("point coordinates should be floats")
	}
	x, _ := xFlt.Val.Float64()
	y, _ := yFlt.Val.Float64()
	return x, y, nil
}

func renderLine(graph *chart.Chart, line *atoms.Expression) error {
	if line.Len() != 1 {
		return fmt.Errorf("expected Line to have one argument, but it has %v arguments", line.Len())
	}
	points, ok := atoms.HeadAssertion(line.GetPart(1), "System`List")
	if !ok {
		return errors.New("expected a nested list")
	}

	series := chart.ContinuousSeries{}
	for _, pointExpr := range points.GetParts()[1:] {
		x, y, err := listToPoint(pointExpr)
		if err != nil {
			return err
		}
		series.XValues = append(series.XValues, x)
		series.YValues = append(series.YValues, y)
	}
	graph.Series = append(graph.Series, series)
	return nil
}

// Render renders the Graphics[] object provided in expr.
func Render(expr expreduceapi.Ex) (chart.Chart, error) {
	graph := chart.Chart{
		Width:  360,
		Height: 220,
		XAxis: chart.XAxis{
			Style: chart.StyleShow(),
		},
		YAxis: chart.YAxis{
			Style: chart.StyleShow(),
		},
	}

	graphics, ok := atoms.HeadAssertion(expr, "System`Graphics")
	if !ok {
		return graph, fmt.Errorf("trying to render a non-Graphics[] expression: %v", expr)
	}

	if graphics.Len() < 1 {
		return graph, errors.New("the Graphics[] expression must have at least one argument")
	}

	nestedList, ok := atoms.HeadAssertion(graphics.GetPart(1), "System`List")
	if !ok {
		return graph, errors.New("expected a nested list")
	}
	// TODO validate length.
	doublyNestedList, ok := atoms.HeadAssertion(nestedList.GetPart(1), "System`List")
	if !ok {
		return graph, errors.New("expected a nested list")
	}
	// TODO validate length.
	directivesList, ok := atoms.HeadAssertion(doublyNestedList.GetPart(3), "System`List")
	if !ok {
		return graph, errors.New("expected a directives list at position 3")
	}

	for _, directive := range directivesList.GetParts()[1:] {
		line, isLine := atoms.HeadAssertion(directive, "System`Line")
		if isLine {
			err := renderLine(&graph, line)
			if err != nil {
				return graph, err
			}
		} else {
			fmt.Printf("Skipping over directive: %v\n", directive)
		}
	}

	return graph, nil
}

// RenderAsPNG renders the Graphics[] object provided in expr as a PNG.
func RenderAsPNG(expr expreduceapi.Ex) (string, error) {
	graph, err := Render(expr)
	if err != nil {
		return "", err
	}

	buffer := bytes.NewBuffer([]byte{})
	err = graph.Render(chart.PNG, buffer)
	if err != nil {
		return "", err
	}
	return buffer.String(), nil
}
