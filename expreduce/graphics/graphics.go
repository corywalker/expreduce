package graphics

import (
	"bytes"
	"errors"
	"fmt"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	chart "github.com/wcharczuk/go-chart"
	"github.com/wcharczuk/go-chart/drawing"
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

func renderLine(graph *chart.Chart, line *atoms.Expression, style *chart.Style) error {
	if line.Len() != 1 {
		return fmt.Errorf("expected Line to have one argument, but it has %v arguments", line.Len())
	}
	points, ok := atoms.HeadAssertion(line.GetPart(1), "System`List")
	if !ok {
		return errors.New("expected a nested list")
	}

	series := chart.ContinuousSeries{}
	series.Style = *style
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

func setColor(colorExpr *atoms.Expression, color *drawing.Color) error {
	if colorExpr.Len() != 3 {
		return fmt.Errorf("expected an RGBColor with 3 arguments")
	}
	for i := 0; i < 3; i++ {
		asFlt, isFlt := colorExpr.GetPart(i + 1).(*atoms.Flt)
		if !isFlt {
			return fmt.Errorf("the RGBColor should have floating point arguments")
		}
		fltVal, _ := asFlt.Val.Float32()
		intVal := uint8(fltVal * 255)
		switch i {
		case 0:
			color.R = intVal
		case 1:
			color.G = intVal
		case 2:
			color.B = intVal
		}
	}
	color.A = 255
	return nil
}

func setOpacity(opacityExpr *atoms.Expression, color *drawing.Color) error {
	if opacityExpr.Len() != 1 {
		return fmt.Errorf("expected an Opacity with 1 argument")
	}
	asFlt, isFlt := opacityExpr.GetPart(1).(*atoms.Flt)
	if !isFlt {
		return fmt.Errorf("the Opacity should have a floating point argument")
	}
	fltVal, _ := asFlt.Val.Float32()
	intVal := uint8(fltVal * 255)
	color.A = intVal
	return nil
}

func setAbsoluteThickness(thicknessExpr *atoms.Expression, thickness *float64) error {
	if thicknessExpr.Len() != 1 {
		return fmt.Errorf("expected an AbsoluteThickness with 1 argument")
	}
	asFlt, isFlt := thicknessExpr.GetPart(1).(*atoms.Flt)
	if !isFlt {
		return fmt.Errorf("the AbsoluteThickness should have a floating point argument")
	}
	fltVal, _ := asFlt.Val.Float64()
	*thickness = fltVal
	return nil
}

func setDirective(style *chart.Style, dir expreduceapi.Ex) error {
	rgbColor, isRgbColor := atoms.HeadAssertion(dir, "System`RGBColor")
	if isRgbColor {
		err := setColor(rgbColor, &style.StrokeColor)
		return err
	}
	opacity, isOpacity := atoms.HeadAssertion(dir, "System`Opacity")
	if isOpacity {
		err := setOpacity(opacity, &style.StrokeColor)
		return err
	}
	thickness, isThickness := atoms.HeadAssertion(dir, "System`AbsoluteThickness")
	if isThickness {
		err := setAbsoluteThickness(thickness, &style.StrokeWidth)
		return err
	}
	fmt.Printf("Skipping over unknown directive: %v\n", dir)
	return nil
}

func renderPrimitive(graph *chart.Chart, primitive expreduceapi.Ex, style *chart.Style) error {
	line, isLine := atoms.HeadAssertion(primitive, "System`Line")
	list, isList := atoms.HeadAssertion(primitive, "System`List")
	directive, isDirective := atoms.HeadAssertion(primitive, "System`Directive")
	if isList {
		newStyle := *style
		for _, subPrimitive := range list.GetParts()[1:] {
			err := renderPrimitive(graph, subPrimitive, &newStyle)
			if err != nil {
				return err
			}
		}
	} else if isDirective {
		for _, directivePart := range directive.GetParts()[1:] {
			err := setDirective(style, directivePart)
			if err != nil {
				return err
			}
		}
	} else if isLine {
		err := renderLine(graph, line, style)
		if err != nil {
			return err
		}
	} else {
		fmt.Printf("Skipping over primitive: %v\n", primitive)
	}
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

	style := chart.Style{
		Show:        true,
		StrokeColor: drawing.ColorBlack,
	}
	renderPrimitive(&graph, graphics.GetPart(1), &style)

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
